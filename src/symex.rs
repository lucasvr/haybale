use llvm_ir::*;
use llvm_ir::instruction::BinaryOp;
use log::{debug, info};
use either::Either;
use reduce::Reduce;
use std::convert::{TryFrom, TryInto};
use std::sync::{Arc, RwLock};

pub use crate::state::{State, Callsite, Location, PathEntry, pretty_bb_name};
use crate::backend::*;
use crate::config::*;
use crate::error::*;
use crate::extend::*;
use crate::layout::*;
use crate::solver_utils::{self, PossibleSolutions};
use crate::project::Project;
use crate::return_value::*;

/// Begin symbolic execution of the function named `funcname`, obtaining an
/// `ExecutionManager`. The function's parameters will start completely
/// unconstrained.
///
/// `project`: The `Project` (set of LLVM modules) in which symbolic execution
/// should take place. In the absence of function hooks (see
/// [`Config`](struct.Config.html)), we will try to enter calls to any functions
/// defined in the `Project`.
pub fn symex_function<'p, B: Backend>(
    funcname: &str,
    project: &'p Project,
    config: Config<'p, B>,
) -> ExecutionManager<'p, B> {
    debug!("Symexing function {}", funcname);
    let (func, module) = project.get_func_by_name(funcname).unwrap_or_else(|| panic!("Failed to find function named {:?}", funcname));
    let bb = func.basic_blocks.get(0).expect("Failed to get entry basic block");
    let start_loc = Location {
        module,
        func,
        bbname: bb.name.clone(),
    };
    let mut state = State::new(project, start_loc, config);
    let bvparams: Vec<_> = func.parameters.iter().map(|param| {
        state.new_bv_with_name(param.name.clone(), size(&param.ty) as u32).unwrap()
    }).collect();
    ExecutionManager::new(state, project, bvparams, &bb)
}

/// An `ExecutionManager` allows you to symbolically explore executions of a
/// function. Conceptually, it is an `Iterator` over possible paths through the
/// function. Calling `next()` on an `ExecutionManager` explores another possible
/// path, returning a [`ReturnValue`](enum.ReturnValue.html) representing the
/// function's symbolic return value at the end of that path.
///
/// Importantly, after any call to `next()`, you can access the `State` resulting
/// from the end of that path using the `state()` or `mut_state()` methods.
///
/// When `next()` returns `None`, there are no more possible paths through the
/// function.
pub struct ExecutionManager<'p, B: Backend> {
    state: State<'p, B>,
    project: &'p Project,
    bvparams: Vec<B::BV>,
    start_bb: &'p BasicBlock,
    /// Whether the `ExecutionManager` is "fresh". A "fresh" `ExecutionManager`
    /// has not yet produced its first path, i.e., `next()` has not been called
    /// on it yet.
    fresh: bool,
}

impl<'p, B: Backend> ExecutionManager<'p, B> {
    fn new(state: State<'p, B>, project: &'p Project, bvparams: Vec<B::BV>, start_bb: &'p BasicBlock) -> Self {
        Self {
            state,
            project,
            bvparams,
            start_bb,
            fresh: true,
        }
    }

    /// Provides access to the `State` resulting from the end of the most recently
    /// explored path (or, if `next()` has never been called on this `ExecutionManager`,
    /// then simply the initial `State` which was passed in).
    pub fn state(&self) -> &State<'p, B> {
        &self.state
    }

    /// Provides mutable access to the underlying `State` (see notes on `state()`).
    /// Changes made to the initial state (before the first call to `next()`) are
    /// "sticky", and will persist through all executions of the function.
    /// However, changes made to a final state (after a call to `next()`) will be
    /// completely wiped away the next time that `next()` is called.
    pub fn mut_state(&mut self) -> &mut State<'p, B> {
        &mut self.state
    }

    /// Provides access to the `BV` objects representing each of the function's parameters
    pub fn param_bvs(&self) -> &Vec<B::BV> {
        &self.bvparams
    }
}

impl<'p, B: Backend> Iterator for ExecutionManager<'p, B> where B: 'p {
    type Item = std::result::Result<ReturnValue<B::BV>, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.fresh {
            self.fresh = false;
            info!("Beginning symex in function {:?}", self.state.cur_loc.func.name);
            self.symex_from_bb_through_end_of_function(self.start_bb).transpose().map(|r| r.map_err(|e|
                format!("Received the following error:\n  {}\nLLVM backtrace:\n{}\n", e, self.state.pretty_llvm_backtrace())
            ))
        } else {
            debug!("ExecutionManager: requesting next path");
            self.backtrack_and_continue().transpose().map(|r| r.map_err(|e|
                format!("Received the following error:\n  {}\nLLVM backtrace:\n{}\n", e, self.state.pretty_llvm_backtrace())
            ))
        }
    }
}

impl<'p, B: Backend> ExecutionManager<'p, B> where B: 'p {
    /// Symex from the current `Location` through the rest of the function.
    /// Returns the `ReturnValue` representing the return value of the function,
    /// or `Ok(None)` if no possible paths were found.
    fn symex_from_cur_loc_through_end_of_function(&mut self) -> Result<Option<ReturnValue<B::BV>>> {
        let bb = self.state.cur_loc.func.get_bb_by_name(&self.state.cur_loc.bbname)
            .unwrap_or_else(|| panic!("Failed to find bb named {:?} in function {:?}", self.state.cur_loc.bbname, self.state.cur_loc.func.name));
        self.symex_from_bb_through_end_of_function(bb)
    }

    /// Symex the given bb, through the rest of the function.
    /// Returns the `ReturnValue` representing the return value of the function,
    /// or `Ok(None)` if no possible paths were found.
    fn symex_from_bb_through_end_of_function(&mut self, bb: &'p BasicBlock) -> Result<Option<ReturnValue<B::BV>>> {
        self.symex_from_inst_in_bb_through_end_of_function(bb, 0)
    }

    /// Symex starting from the given `inst` index in the given bb, through the rest of the function.
    /// Returns the `ReturnValue` representing the return value of the function,
    /// or `Ok(None)` if no possible paths were found.
    fn symex_from_inst_in_bb_through_end_of_function(&mut self, bb: &'p BasicBlock, inst: usize) -> Result<Option<ReturnValue<B::BV>>> {
        assert_eq!(bb.name, self.state.cur_loc.bbname);
        debug!("Symexing basic block {:?} in function {}", bb.name, self.state.cur_loc.func.name);
        self.state.record_path_entry();
        for (instnum, inst) in bb.instrs.iter().skip(inst).enumerate() {
            let result = if let Ok(binop) = inst.clone().try_into() {
                self.symex_binop(&binop)
            } else {
                match inst {
                    Instruction::ICmp(icmp) => self.symex_icmp(icmp),
                    Instruction::Load(load) => self.symex_load(load),
                    Instruction::Store(store) => self.symex_store(store),
                    Instruction::GetElementPtr(gep) => self.symex_gep(gep),
                    Instruction::Alloca(alloca) => self.symex_alloca(alloca),
                    Instruction::ExtractElement(ee) => self.symex_extractelement(ee),
                    Instruction::InsertElement(ie) => self.symex_insertelement(ie),
                    Instruction::ShuffleVector(sv) => self.symex_shufflevector(sv),
                    Instruction::ZExt(zext) => self.symex_zext(zext),
                    Instruction::SExt(sext) => self.symex_sext(sext),
                    Instruction::Trunc(trunc) => self.symex_trunc(trunc),
                    Instruction::PtrToInt(pti) => self.symex_cast_op(pti),
                    Instruction::IntToPtr(itp) => self.symex_cast_op(itp),
                    Instruction::BitCast(bitcast) => self.symex_cast_op(bitcast),
                    Instruction::Phi(phi) => self.symex_phi(phi),
                    Instruction::Select(select) => self.symex_select(select),
                    Instruction::Call(call) => match self.symex_call(call, instnum) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(()),
                        Ok(Some(symexresult)) => return Ok(Some(symexresult)),
                    },
                    _ => return Err(Error::UnsupportedInstruction(format!("instruction {:?}", inst))),
                }
            };
            match result {
                Ok(_) => {},  // no error, we can continue
                Err(Error::Unsat) | Err(Error::LoopBoundExceeded) => {
                    // we can't continue down this path anymore
                    return self.backtrack_and_continue();
                }
                Err(e) => return Err(e),  // propagate any other errors
            };
        }
        match &bb.term {
            Terminator::Ret(ret) => self.symex_return(ret).map(Some),
            Terminator::Br(br) => self.symex_br(br),
            Terminator::CondBr(condbr) => self.symex_condbr(condbr),
            Terminator::Switch(switch) => self.symex_switch(switch),
            term => Err(Error::UnsupportedInstruction(format!("terminator {:?}", term))),
        }
    }

    /// Revert to the most recent backtrack point, then continue execution from that point.
    /// Will continue not just to the end of the function containing the backtrack point,
    /// but (using the saved callstack) all the way back to the end of the top-level function.
    ///
    /// Returns the `ReturnValue` representing the final return value, or
    /// `Ok(None)` if no possible paths were found.
    fn backtrack_and_continue(&mut self) -> Result<Option<ReturnValue<B::BV>>> {
        if self.state.revert_to_backtracking_point()? {
            info!("Reverted to backtrack point; {} more backtrack points available", self.state.count_backtracking_points());
            info!("Continuing in bb {} in function {:?}, module {:?}", pretty_bb_name(&self.state.cur_loc.bbname), self.state.cur_loc.func.name, self.state.cur_loc.module.name);
            self.symex_from_inst_in_cur_loc(0)
        } else {
            // No backtrack points (and therefore no paths) remain
            Ok(None)
        }
    }

    /// Symex starting from the given `inst` index in the current bb, returning
    /// (using the saved callstack) all the way back to the end of the top-level
    /// function.
    ///
    /// Returns the `ReturnValue` representing the final return value, or
    /// `Ok(None)` if no possible paths were found.
    fn symex_from_inst_in_cur_loc(&mut self, inst: usize) -> Result<Option<ReturnValue<B::BV>>> {
        let bb = self.state.cur_loc.func.get_bb_by_name(&self.state.cur_loc.bbname)
            .unwrap_or_else(|| panic!("Failed to find bb named {:?} in function {:?}", self.state.cur_loc.bbname, self.state.cur_loc.func.name));
        self.symex_from_inst_in_bb(&bb, inst)
    }

    /// Symex starting from the given `inst` index in the given bb, returning
    /// (using the saved callstack) all the way back to the end of the top-level
    /// function.
    ///
    /// Returns the `ReturnValue` representing the final return value, or
    /// `Ok(None)` if no possible paths were found.
    fn symex_from_inst_in_bb(&mut self, bb: &'p BasicBlock, inst: usize) -> Result<Option<ReturnValue<B::BV>>> {
        match self.symex_from_inst_in_bb_through_end_of_function(bb, inst)? {
            Some(symexresult) => match self.state.pop_callsite() {
                Some(callsite) => {
                    // Return to callsite
                    info!("Leaving function {:?}, continuing in caller {:?} (bb {}) in module {:?}",
                        self.state.cur_loc.func.name,
                        callsite.loc.func.name,
                        pretty_bb_name(&callsite.loc.bbname),
                        callsite.loc.module.name,
                    );
                    self.state.cur_loc = callsite.loc.clone();
                    // Assign the returned value as the result of the caller's call instruction
                    match symexresult {
                        ReturnValue::Return(bv) => {
                            let call: &Instruction = callsite.loc.func
                                .get_bb_by_name(&callsite.loc.bbname)
                                .expect("Malformed callsite (bb not found)")
                                .instrs
                                .get(callsite.inst)
                                .expect("Malformed callsite (inst out of range)");
                            let call: &instruction::Call = match call {
                                Instruction::Call(call) => call,
                                _ => panic!("Malformed callsite: expected a Call, got {:?}", call),
                            };
                            if self.state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), bv).is_err() {
                                // This path is dead, try backtracking again
                                return self.backtrack_and_continue();
                            };
                        },
                        ReturnValue::ReturnVoid => { },
                    };
                    // Continue execution in caller, with the instruction after the call instruction
                    self.symex_from_inst_in_cur_loc(callsite.inst + 1)
                },
                None => {
                    // No callsite to return to, so we're done
                    Ok(Some(symexresult))
                }
            },
            None => {
                // This path is dead, try backtracking again
                self.backtrack_and_continue()
            },
        }
    }

    fn binop_to_btorbinop<'a, V: BV + 'a>(bop: &instruction::groups::BinaryOp) -> Result<Box<dyn for<'b> Fn(&'b V, &'b V) -> V + 'a>> {
        match bop {
            // TODO: how to not clone the inner instruction here
            instruction::groups::BinaryOp::Add(_) => Ok(Box::new(V::add)),
            instruction::groups::BinaryOp::Sub(_) => Ok(Box::new(V::sub)),
            instruction::groups::BinaryOp::Mul(_) => Ok(Box::new(V::mul)),
            instruction::groups::BinaryOp::UDiv(_) => Ok(Box::new(V::udiv)),
            instruction::groups::BinaryOp::SDiv(_) => Ok(Box::new(V::sdiv)),
            instruction::groups::BinaryOp::URem(_) => Ok(Box::new(V::urem)),
            instruction::groups::BinaryOp::SRem(_) => Ok(Box::new(V::srem)),
            instruction::groups::BinaryOp::And(_) => Ok(Box::new(V::and)),
            instruction::groups::BinaryOp::Or(_) => Ok(Box::new(V::or)),
            instruction::groups::BinaryOp::Xor(_) => Ok(Box::new(V::xor)),
            instruction::groups::BinaryOp::Shl(_) => Ok(Box::new(V::sll)),
            instruction::groups::BinaryOp::LShr(_) => Ok(Box::new(V::srl)),
            instruction::groups::BinaryOp::AShr(_) => Ok(Box::new(V::sra)),
            _ => Err(Error::UnsupportedInstruction(format!("BinaryOp {:?}", bop))),
        }
    }

    fn intpred_to_btorpred(pred: IntPredicate) -> Box<dyn Fn(&B::BV, &B::BV) -> B::BV + 'p> {
        match pred {
            IntPredicate::EQ => Box::new(B::BV::_eq),
            IntPredicate::NE => Box::new(B::BV::_ne),
            IntPredicate::UGT => Box::new(B::BV::ugt),
            IntPredicate::UGE => Box::new(B::BV::ugte),
            IntPredicate::ULT => Box::new(B::BV::ult),
            IntPredicate::ULE => Box::new(B::BV::ulte),
            IntPredicate::SGT => Box::new(B::BV::sgt),
            IntPredicate::SGE => Box::new(B::BV::sgte),
            IntPredicate::SLT => Box::new(B::BV::slt),
            IntPredicate::SLE => Box::new(B::BV::slte),
        }
    }

    // Apply the given unary scalar operation to a vector
    fn unary_on_vector<F>(in_vector: &B::BV, num_elements: u32, mut op: F) -> Result<B::BV>
        where F: FnMut(&B::BV) -> B::BV
    {
        let in_vector_size = in_vector.get_width();
        assert_eq!(in_vector_size % num_elements, 0);
        let in_el_size = in_vector_size / num_elements;
        let in_scalars = (0 .. num_elements).map(|i| in_vector.slice((i+1)*in_el_size - 1, i*in_el_size));
        let out_scalars = in_scalars.map(|s| op(&s));
        out_scalars.reduce(|a,b| b.concat(&a)).ok_or_else(|| Error::OtherError("Vector operation with 0 elements".to_owned()))
    }

    // Apply the given binary scalar operation to a vector
    fn binary_on_vector<F>(in_vector_0: &B::BV, in_vector_1: &B::BV, num_elements: u32, mut op: F) -> Result<B::BV>
        where F: for<'a> FnMut(&'a B::BV, &'a B::BV) -> B::BV
    {
        let in_vector_0_size = in_vector_0.get_width();
        let in_vector_1_size = in_vector_1.get_width();
        if in_vector_0_size != in_vector_1_size {
            return Err(Error::MalformedInstruction(format!("Binary operation's vector operands are different total sizes: {} vs. {}", in_vector_0_size, in_vector_1_size)));
        }
        let in_vector_size = in_vector_0_size;
        assert_eq!(in_vector_size % num_elements, 0);
        let in_el_size = in_vector_size / num_elements;
        let in_scalars_0 = (0 .. num_elements).map(|i| in_vector_0.slice((i+1)*in_el_size - 1, i*in_el_size));
        let in_scalars_1 = (0 .. num_elements).map(|i| in_vector_1.slice((i+1)*in_el_size - 1, i*in_el_size));
        let out_scalars = in_scalars_0.zip(in_scalars_1).map(|(s0,s1)| op(&s0, &s1));
        out_scalars.reduce(|a,b| b.concat(&a)).ok_or_else(|| Error::MalformedInstruction("Binary operation on vectors with 0 elements".to_owned()))
    }

    fn symex_binop(&mut self, bop: &instruction::groups::BinaryOp) -> Result<()> {
        debug!("Symexing binop {:?}", bop);
        // We expect these binops to only operate on integers or vectors of integers
        let op0 = &bop.get_operand0();
        let op1 = &bop.get_operand1();
        let op0_type = op0.get_type();
        let op1_type = op1.get_type();
        if op0_type != op1_type {
            return Err(Error::MalformedInstruction(format!("Expected binary op to have two operands of same type, but have types {:?} and {:?}", op0_type, op1_type)));
        }
        let op_type = op0_type;
        let btorop0 = self.state.operand_to_bv(op0)?;
        let btorop1 = self.state.operand_to_bv(op1)?;
        let btoroperation = Self::binop_to_btorbinop(bop)?;
        match op_type {
            Type::IntegerType { .. } => {
                self.state.record_bv_result(bop, btoroperation(&btorop0, &btorop1))
            },
            Type::VectorType { element_type, num_elements } => {
                match *element_type {
                    Type::IntegerType { .. } => {
                        self.state.record_bv_result(bop, Self::binary_on_vector(&btorop0, &btorop1, num_elements as u32, btoroperation)?)
                    },
                    ty => Err(Error::MalformedInstruction(format!("Expected binary operation's vector operands to have integer elements, but elements are type {:?}", ty))),
                }
            }
            ty => Err(Error::MalformedInstruction(format!("Expected binary operation to have operands of type integer or vector of integers, but got type {:?}", ty))),
        }
    }

    fn symex_icmp(&mut self, icmp: &'p instruction::ICmp) -> Result<()> {
        debug!("Symexing icmp {:?}", icmp);
        let btorfirstop = self.state.operand_to_bv(&icmp.operand0)?;
        let btorsecondop = self.state.operand_to_bv(&icmp.operand1)?;
        let btorpred = Self::intpred_to_btorpred(icmp.predicate);
        let op0_type = icmp.operand0.get_type();
        let op1_type = icmp.operand1.get_type();
        if op0_type != op1_type {
            return Err(Error::MalformedInstruction(format!("Expected icmp to compare two operands of same type, but have types {:?} and {:?}", op0_type, op1_type)));
        }
        match icmp.get_type() {
            Type::IntegerType { bits } if bits == 1 => match op0_type {
                Type::IntegerType { .. } | Type::VectorType { .. } | Type::PointerType { .. } => {
                    self.state.record_bv_result(icmp, btorpred(&btorfirstop, &btorsecondop))
                },
                ty => Err(Error::MalformedInstruction(format!("Expected ICmp to have operands of type integer, pointer, or vector of integers, but got type {:?}", ty))),
            },
            Type::VectorType { element_type, num_elements } => match *element_type {
                Type::IntegerType { bits } if bits == 1 => match op0_type {
                    Type::IntegerType { .. } | Type::VectorType { .. } | Type::PointerType { .. } => {
                        let zero = B::BV::zero(self.state.solver.clone(), 1);
                        let one = B::BV::one(self.state.solver.clone(), 1);
                        let final_bv = Self::binary_on_vector(&btorfirstop, &btorsecondop, num_elements as u32, |a,b| btorpred(a,b).cond_bv(&one, &zero))?;
                        self.state.record_bv_result(icmp, final_bv)
                    },
                    ty => Err(Error::MalformedInstruction(format!("Expected ICmp to have operands of type integer, pointer, or vector of integers, but got type {:?}", ty))),
                },
                ty => Err(Error::MalformedInstruction(format!("Expected ICmp result type to be i1 or vector of i1; got vector of {:?}", ty))),
            }
            ty => Err(Error::MalformedInstruction(format!("Expected ICmp result type to be i1 or vector of i1; got {:?}", ty))),
        }
   }

    fn symex_zext(&mut self, zext: &'p instruction::ZExt) -> Result<()> {
        debug!("Symexing zext {:?}", zext);
        match zext.operand.get_type() {
            Type::IntegerType { bits } => {
                let btorop = self.state.operand_to_bv(&zext.operand)?;
                let source_size = bits;
                let dest_size = size(&zext.get_type()) as u32;
                self.state.record_bv_result(zext, btorop.zext(dest_size - source_size))
            },
            Type::VectorType { element_type, num_elements } => {
                let in_vector = self.state.operand_to_bv(&zext.operand)?;
                let in_el_size = size(&element_type) as u32;
                let out_el_size = match zext.get_type() {
                    Type::VectorType { element_type: out_el_type, num_elements: out_num_els } => {
                        if out_num_els != num_elements {
                            return Err(Error::MalformedInstruction(format!("ZExt operand is a vector of {} elements but output is a vector of {} elements", num_elements, out_num_els)));
                        }
                        size(&out_el_type) as u32
                    },
                    ty => return Err(Error::MalformedInstruction(format!("ZExt operand is a vector type, but output is not: it is {:?}", ty))),
                };
                let final_bv = Self::unary_on_vector(&in_vector, num_elements as u32, |el| {
                    el.zext(out_el_size - in_el_size)
                })?;
                self.state.record_bv_result(zext, final_bv)
            },
            ty => Err(Error::MalformedInstruction(format!("Expected ZExt operand type to be integer or vector of integers; got {:?}", ty))),
        }
    }

    fn symex_sext(&mut self, sext: &'p instruction::SExt) -> Result<()> {
        debug!("Symexing sext {:?}", sext);
        match sext.operand.get_type() {
            Type::IntegerType { bits } => {
                let btorop = self.state.operand_to_bv(&sext.operand)?;
                let source_size = bits;
                let dest_size = size(&sext.get_type()) as u32;
                self.state.record_bv_result(sext, btorop.sext(dest_size - source_size))
            },
            Type::VectorType { element_type, num_elements } => {
                let in_vector = self.state.operand_to_bv(&sext.operand)?;
                let in_el_size = size(&element_type) as u32;
                let out_el_size = match sext.get_type() {
                    Type::VectorType { element_type: out_el_type, num_elements: out_num_els } => {
                        if out_num_els != num_elements {
                            return Err(Error::MalformedInstruction(format!("SExt operand is a vector of {} elements but output is a vector of {} elements", num_elements, out_num_els)));
                        }
                        size(&out_el_type) as u32
                    },
                    ty => return Err(Error::MalformedInstruction(format!("SExt operand is a vector type, but output is not: it is {:?}", ty))),
                };
                let final_bv = Self::unary_on_vector(&in_vector, num_elements as u32, |el| {
                    el.sext(out_el_size - in_el_size)
                })?;
                self.state.record_bv_result(sext, final_bv)
            },
            ty => Err(Error::MalformedInstruction(format!("Expected SExt operand type to be integer or vector of integers; got {:?}", ty))),
        }
    }

    fn symex_trunc(&mut self, trunc: &'p instruction::Trunc) -> Result<()> {
        debug!("Symexing trunc {:?}", trunc);
        match trunc.operand.get_type() {
            Type::IntegerType { .. } => {
                let btorop = self.state.operand_to_bv(&trunc.operand)?;
                let dest_size = size(&trunc.get_type()) as u32;
                self.state.record_bv_result(trunc, btorop.slice(dest_size-1, 0))
            },
            Type::VectorType { num_elements, .. } => {
                let in_vector = self.state.operand_to_bv(&trunc.operand)?;
                let dest_el_size = match trunc.get_type() {
                    Type::VectorType { element_type: out_el_type, num_elements: out_num_els } => {
                        if out_num_els != num_elements {
                            return Err(Error::MalformedInstruction(format!("Trunc operand is a vector of {} elements but output is a vector of {} elements", num_elements, out_num_els)));
                        }
                        size(&out_el_type) as u32
                    },
                    ty => return Err(Error::MalformedInstruction(format!("Trunc operand is a vector type, but output is not: it is {:?}", ty))),
                };
                let final_bv = Self::unary_on_vector(&in_vector, num_elements as u32, |el| el.slice(dest_el_size-1, 0))?;
                self.state.record_bv_result(trunc, final_bv)
            },
            ty => Err(Error::MalformedInstruction(format!("Expected Trunc operand type to be integer or vector of integers; got {:?}", ty))),
        }
    }

    /// Use this for any unary operation that can be treated as a cast
    fn symex_cast_op(&mut self, cast: &'p impl instruction::UnaryOp) -> Result<()> {
        debug!("Symexing cast op {:?}", cast);
        let btorop = self.state.operand_to_bv(&cast.get_operand())?;
        self.state.record_bv_result(cast, btorop)  // from Boolector's perspective a cast is simply a no-op; the bit patterns are equal
    }

    fn symex_load(&mut self, load: &'p instruction::Load) -> Result<()> {
        debug!("Symexing load {:?}", load);
        let btoraddr = self.state.operand_to_bv(&load.address)?;
        let dest_size = size(&load.get_type());
        self.state.record_bv_result(load, self.state.read(&btoraddr, dest_size as u32)?)
    }

    fn symex_store(&mut self, store: &'p instruction::Store) -> Result<()> {
        debug!("Symexing store {:?}", store);
        let btorval = self.state.operand_to_bv(&store.value)?;
        let btoraddr = self.state.operand_to_bv(&store.address)?;
        self.state.write(&btoraddr, btorval)
    }

    fn symex_gep(&mut self, gep: &'p instruction::GetElementPtr) -> Result<()> {
        debug!("Symexing gep {:?}", gep);
        match gep.get_type() {
            Type::PointerType { .. } => {
                let btorbase = self.state.operand_to_bv(&gep.address)?;
                let offset = Self::get_offset_recursive(&self.state, gep.indices.iter(), &gep.address.get_type(), btorbase.get_width())?;
                self.state.record_bv_result(gep, btorbase.add(&offset))
            },
            Type::VectorType { .. } => Err(Error::UnsupportedInstruction("GEP calculating a vector of pointers".to_owned())),
            ty => Err(Error::MalformedInstruction(format!("Expected GEP result type to be pointer or vector of pointers; got {:?}", ty))),
        }
    }

    /// Get the offset of the element (in bytes, as a `BV` of `result_bits` bits)
    fn get_offset_recursive(state: &State<'p, B>, mut indices: impl Iterator<Item = &'p Operand>, base_type: &Type, result_bits: u32) -> Result<B::BV> {
        match indices.next() {
            None => Ok(BV::zero(state.solver.clone(), result_bits)),
            Some(index) => match base_type {
                Type::PointerType { .. } | Type::ArrayType { .. } | Type::VectorType { .. } => {
                    let index = zero_extend_to_bits(state.operand_to_bv(index)?, result_bits);
                    let (offset, nested_ty) = get_offset_bv_index(base_type, &index, state.solver.clone())?;
                    Self::get_offset_recursive(state, indices, nested_ty, result_bits)
                        .map(|bv| bv.add(&offset))
                },
                Type::StructType { .. } => match index {
                    Operand::ConstantOperand(Constant::Int { value: index, .. }) => {
                        let (offset, nested_ty) = get_offset_constant_index(base_type, *index as usize)?;
                        Self::get_offset_recursive(state, indices, &nested_ty, result_bits)
                            .map(|bv| bv.add(&B::BV::from_u32(state.solver.clone(), offset as u32, result_bits)))
                    },
                    _ => Err(Error::MalformedInstruction(format!("Expected index into struct type to be constant, but got index {:?}", index))),
                },
                Type::NamedStructType { ty, .. } => {
                    let arc: Arc<RwLock<Type>> = ty.as_ref()
                        .ok_or_else(|| Error::MalformedInstruction("get_offset on an opaque struct type".to_owned()))?
                        .upgrade()
                        .expect("Failed to upgrade weak reference");
                    let actual_ty: &Type = &arc.read().unwrap();
                    if let Type::StructType { .. } = actual_ty {
                        // this code copied from the StructType case
                        match index {
                            Operand::ConstantOperand(Constant::Int { value: index, .. }) => {
                                let (offset, nested_ty) = get_offset_constant_index(base_type, *index as usize)?;
                                Self::get_offset_recursive(state, indices, &nested_ty, result_bits)
                                    .map(|bv| bv.add(&B::BV::from_u32(state.solver.clone(), offset as u32, result_bits)))
                            },
                            _ => Err(Error::MalformedInstruction(format!("Expected index into struct type to be constant, but got index {:?}", index))),
                        }
                    } else {
                        Err(Error::MalformedInstruction(format!("Expected NamedStructType inner type to be a StructType, but got {:?}", actual_ty)))
                    }
                }
                _ => panic!("get_offset_recursive with base type {:?}", base_type),
            }
        }
    }

    fn symex_alloca(&mut self, alloca: &'p instruction::Alloca) -> Result<()> {
        debug!("Symexing alloca {:?}", alloca);
        match &alloca.num_elements {
            Operand::ConstantOperand(Constant::Int { value: num_elements, .. }) => {
                let allocation_size = size(&alloca.allocated_type) as u64 * num_elements;
                let allocated = self.state.allocate(allocation_size);
                self.state.record_bv_result(alloca, allocated)
            },
            op => Err(Error::UnsupportedInstruction(format!("Alloca with num_elements not a constant int: {:?}", op))),
        }
    }

    fn symex_extractelement(&mut self, ee: &'p instruction::ExtractElement) -> Result<()> {
        debug!("Symexing extractelement {:?}", ee);
        let vector = self.state.operand_to_bv(&ee.vector)?;
        match &ee.index {
            Operand::ConstantOperand(Constant::Int { value: index, .. }) => {
                let index = *index as u32;
                match ee.vector.get_type() {
                    Type::VectorType { element_type, num_elements } => {
                        if index >= num_elements as u32 {
                            Err(Error::MalformedInstruction(format!("ExtractElement index out of range: index {} with {} elements", index, num_elements)))
                        } else {
                            let el_size = size(&element_type) as u32;
                            self.state.record_bv_result(ee, vector.slice((index+1)*el_size - 1, index*el_size))
                        }
                    },
                    ty => Err(Error::MalformedInstruction(format!("Expected ExtractElement vector to be a vector type, got {:?}", ty))),
                }
            },
            op => Err(Error::UnsupportedInstruction(format!("ExtractElement with index not a constant int: {:?}", op))),
        }
    }

    fn symex_insertelement(&mut self, ie: &'p instruction::InsertElement) -> Result<()> {
        debug!("Symexing insertelement {:?}", ie);
        let vector = self.state.operand_to_bv(&ie.vector)?;
        let element = self.state.operand_to_bv(&ie.element)?;
        match &ie.index {
            Operand::ConstantOperand(Constant::Int { value: index, .. }) => {
                let index = *index as u32;
                match ie.vector.get_type() {
                    Type::VectorType { element_type, num_elements } => {
                        if index >= num_elements as u32 {
                            Err(Error::MalformedInstruction(format!("InsertElement index out of range: index {} with {} elements", index, num_elements)))
                        } else {
                            let vec_size = vector.get_width();
                            let highest_bit_index = vec_size - 1;
                            let el_size = size(&element_type) as u32;
                            assert_eq!(vec_size, el_size * num_elements as u32);
                            let insertion_bitindex_low = index * el_size;  // lowest bit number in the vector which will be overwritten
                            let insertion_bitindex_high = (index+1) * el_size - 1;  // highest bit number in the vector which will be overwritten

                            // mask_clear is 0's in the bit positions that will be written, 1's elsewhere
                            let zeroes = B::BV::zero(self.state.solver.clone(), el_size);
                            let mask_clear = if insertion_bitindex_high == highest_bit_index {
                                if insertion_bitindex_low == 0 {
                                    zeroes
                                } else {
                                    zeroes.concat(&B::BV::ones(self.state.solver.clone(), insertion_bitindex_low))
                                }
                            } else {
                                let top = B::BV::ones(self.state.solver.clone(), highest_bit_index - insertion_bitindex_high)
                                    .concat(&zeroes);
                                if insertion_bitindex_low == 0 {
                                    top
                                } else {
                                    top.concat(&B::BV::ones(self.state.solver.clone(), insertion_bitindex_low))
                                }
                            };

                            // mask_insert is the insertion data in the appropriate bit positions, 0's elsewhere
                            let top = zero_extend_to_bits(element, vec_size - insertion_bitindex_low);
                            let mask_insert = if insertion_bitindex_low == 0 {
                                top
                            } else {
                                top.concat(&B::BV::zero(self.state.solver.clone(), insertion_bitindex_low))
                            };

                            let with_insertion = vector
                                .and(&mask_clear)  // zero out the element we'll be writing
                                .or(&mask_insert);  // write the data into the element's position

                            self.state.record_bv_result(ie, with_insertion)
                        }
                    },
                    ty => Err(Error::MalformedInstruction(format!("Expected InsertElement vector to be a vector type, got {:?}", ty))),
                }
            },
            op => Err(Error::UnsupportedInstruction(format!("InsertElement with index not a constant int: {:?}", op))),
        }
    }

    fn symex_shufflevector(&mut self, sv: &'p instruction::ShuffleVector) -> Result<()> {
        debug!("Symexing shufflevector {:?}", sv);
        let op0_type = sv.operand0.get_type();
        let op1_type = sv.operand1.get_type();
        if op0_type != op1_type {
            return Err(Error::MalformedInstruction(format!("Expected ShuffleVector operands to be exactly the same type, but they are {:?} and {:?}", op0_type, op1_type)));
        }
        let op_type = op0_type;
        match op_type {
            Type::VectorType { element_type, num_elements } => {
                let mask: Vec<u32> = match &sv.mask {
                    Constant::Vector(mask) => mask.iter()
                        .map(|c| match c {
                            Constant::Int { value: idx, .. } => Ok(*idx as u32),
                            Constant::Undef(_) => Ok(0),
                            _ => Err(Error::UnsupportedInstruction(format!("ShuffleVector with a mask entry which is not a Constant::Int or Constant::Undef but instead {:?}", c))),
                        })
                        .collect::<Result<Vec<u32>>>()?,
                    Constant::AggregateZero(ty) | Constant::Undef(ty) => match ty {
                        Type::VectorType { num_elements, .. } => itertools::repeat_n(0, *num_elements).collect(),
                        _ => return Err(Error::MalformedInstruction(format!("Expected ShuffleVector mask (which is an AggregateZero or Undef) to have vector type, but its type is {:?}", ty))),
                    },
                    c => return Err(Error::MalformedInstruction(format!("Expected ShuffleVector mask to be a Constant::Vector, Constant::AggregateZero, or Constant::Undef, but got {:?}", c))),
                };
                let op0 = self.state.operand_to_bv(&sv.operand0)?;
                let op1 = self.state.operand_to_bv(&sv.operand1)?;
                assert_eq!(op0.get_width(), op1.get_width());
                let el_size = size(&element_type) as u32;
                let num_elements = num_elements as u32;
                assert_eq!(op0.get_width(), el_size * num_elements);
                let final_bv = mask.into_iter()
                    .map(|idx| {
                        if idx < num_elements {
                            op0.slice((idx+1) * el_size - 1, idx * el_size)
                        } else {
                            let idx = idx - num_elements;
                            op1.slice((idx+1) * el_size - 1, idx * el_size)
                        }
                    })
                    .reduce(|a,b| b.concat(&a)).ok_or_else(|| Error::MalformedInstruction("ShuffleVector mask had 0 elements".to_owned()))?;
                self.state.record_bv_result(sv, final_bv)
            },
            ty => Err(Error::MalformedInstruction(format!("Expected ShuffleVector operands to be vectors, got {:?}", ty))),
        }
    }

    /// `instnum`: the index in the current `BasicBlock` of the given `Call` instruction.
    /// If the returned value is `Ok(Some(_))`, then this is the final return value of the top-level function (we had backtracking and finished on a different path).
    /// If the returned value is `Ok(None)`, then we finished the call normally, and execution should continue from here.
    fn symex_call(&mut self, call: &'p instruction::Call, instnum: usize) -> Result<Option<ReturnValue<B::BV>>> {
        debug!("Symexing call {:?}", call);
        use crate::global_allocations::Callable;
        let funcname_or_hook: Either<&str, FunctionHook<B>> = match &call.function {
            // the first two cases are really just optimizations for the third case; things should still work without the first two lines
            Either::Right(Operand::ConstantOperand(Constant::GlobalReference { name: Name::Name(name), .. })) => Either::Left(name),
            Either::Right(Operand::ConstantOperand(Constant::GlobalReference { name, .. })) => panic!("Function with a numbered name: {:?}", name),
            Either::Right(operand) => {
                match self.state.interpret_as_function_ptr(self.state.operand_to_bv(&operand)?, 1)? {
                    PossibleSolutions::AtLeast(_) => return Err(Error::OtherError("calling a function pointer which has multiple possible targets".to_owned())),  // there must be at least 2 targets since we passed n==1 to `interpret_as_function_ptr`
                    PossibleSolutions::Exactly(v) => match v.iter().next() {
                        None => return Err(Error::Unsat),  // no valid solutions for the function pointer
                        Some(Callable::LLVMFunction(f)) => Either::Left(&f.name),
                        Some(Callable::FunctionHook(h)) => Either::Right(h.clone()),
                    }
                }
            },
            Either::Left(_) => return Err(Error::UnsupportedInstruction("inline assembly".to_owned())),
        };
        // If a hook is active for this function, `hook` will be `Some`. If
        // we're hooking a real function as opposed to a function pointer,
        // `funcname` will hold the name of the function being hooked.
        let (hook, funcname): (Option<FunctionHook<B>>, Option<&str>) = match funcname_or_hook {
            Either::Left(funcname) => (self.state.config.function_hooks.get_hook_for(funcname).cloned(), Some(funcname)),
            Either::Right(ref hook) => (Some(hook.clone()), None),
        };
        // If a hook is active, process the hook
        if let Some(hook) = hook {
            match hook.call_hook(&mut self.state, call)? {
                ReturnValue::ReturnVoid => {
                    if call.get_type() != Type::VoidType {
                        let funcname = funcname.unwrap_or("a function pointer");
                        return Err(Error::OtherError(format!("Hook for {:?} returned void but call needs a return value", funcname)));
                    }
                },
                ReturnValue::Return(retval) => {
                    if call.get_type() == Type::VoidType {
                        let funcname = funcname.unwrap_or("a function pointer");
                        return Err(Error::OtherError(format!("Hook for {:?} returned a value but call is void-typed", funcname)));
                    } else {
                        // can't quite use `state.record_bv_result(call, retval)?` because Call is not HasResult
                        self.state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), retval)?;
                    }
                }
            }
            return Ok(None);
        }
        // If we're still here, there's no hook active
        let funcname = funcname_or_hook.left().unwrap();  // must have been an Either::Left at this point
        if let Some((callee, callee_mod)) = self.project.get_func_by_name(funcname) {
            assert_eq!(call.arguments.len(), callee.parameters.len());
            let btorargs: Vec<B::BV> = call.arguments.iter()
                .map(|arg| self.state.operand_to_bv(&arg.0))  // have to do this before changing state.cur_loc, so that the lookups happen in the caller function
                .collect::<Result<Vec<B::BV>>>()?;
            let saved_loc = self.state.cur_loc.clone();
            self.state.push_callsite(instnum);
            let bb = callee.basic_blocks.get(0).expect("Failed to get entry basic block");
            self.state.cur_loc = Location {
                module: callee_mod,
                func: callee,
                bbname: bb.name.clone(),
            };
            for (btorarg, param) in btorargs.into_iter().zip(callee.parameters.iter()) {
                self.state.assign_bv_to_name(param.name.clone(), btorarg)?;  // have to do the assign_bv_to_name calls after changing state.cur_loc, so that the variables are created in the callee function
            }
            info!("Entering function {:?} in module {:?}", funcname, &callee_mod.name);
            let returned_bv = self.symex_from_bb_through_end_of_function(&bb)?.ok_or(Error::Unsat)?;  // if symex_from_bb_through_end_of_function() returns `None`, this path is unsat
            match self.state.pop_callsite() {
                None => Ok(Some(returned_bv)),  // if there was no callsite to pop, then we finished elsewhere. See notes on `symex_call()`
                Some(Callsite { ref loc, inst }) if loc == &saved_loc && inst == instnum => {
                    self.state.cur_loc = saved_loc;
                    self.state.record_path_entry();
                    match returned_bv {
                        ReturnValue::Return(bv) => {
                            // can't quite use `state.record_bv_result(call, bv)?` because Call is not HasResult
                            self.state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), bv)?;
                        },
                        ReturnValue::ReturnVoid => assert_eq!(call.dest, None),
                    };
                    debug!("Completed ordinary return to caller");
                    info!("Leaving function {:?}, continuing in caller {:?} (bb {}) in module {:?}", funcname, &self.state.cur_loc.func.name, pretty_bb_name(&self.state.cur_loc.bbname), &self.state.cur_loc.module.name);
                    Ok(None)
                },
                Some(callsite) => panic!("Received unexpected callsite {:?}", callsite),
            }
        } else if funcname.starts_with("llvm.memset")
            || funcname.starts_with("__memset")
        {
            symex_memset(&mut self.state, call)?;
            Ok(None)
        } else if funcname.starts_with("llvm.memcpy")
            || funcname.starts_with("llvm.memmove")
            || funcname.starts_with("__memcpy")
        {
            // Our memcpy implementation also works for memmove
            symex_memcpy(&mut self.state, call)?;
            Ok(None)
        } else if funcname.starts_with("llvm.objectsize") {
            symex_objectsize(&mut self.state, call)?;
            Ok(None)
        } else if funcname.starts_with("llvm.lifetime")
            || funcname.starts_with("llvm.invariant")
            || funcname.starts_with("llvm.launder.invariant")
            || funcname.starts_with("llvm.strip.invariant")
            || funcname.starts_with("llvm.dbg")
        {
            Ok(None) // these are all safe to ignore
        } else {
            Err(Error::FunctionNotFound(funcname.to_owned()))
        }
    }

    /// Returns the `ReturnValue` representing the return value
    fn symex_return(&self, ret: &'p terminator::Ret) -> Result<ReturnValue<B::BV>> {
        debug!("Symexing return {:?}", ret);
        Ok(ret.return_operand
            .as_ref()
            .map(|op| self.state.operand_to_bv(op))
            .transpose()?  // turns Option<Result<_>> into Result<Option<_>>, then ?'s away the Result
            .map(ReturnValue::Return)
            .unwrap_or(ReturnValue::ReturnVoid))
    }

    /// Continues to the target of the `Br` and eventually returns the new `ReturnValue`
    /// representing the return value of the function (when it reaches the end of the
    /// function), or `Ok(None)` if no possible paths were found.
    fn symex_br(&mut self, br: &'p terminator::Br) -> Result<Option<ReturnValue<B::BV>>> {
        debug!("Symexing br {:?}", br);
        self.state.cur_loc.bbname = br.dest.clone();
        self.symex_from_cur_loc_through_end_of_function()
    }

    /// Continues to the target(s) of the `CondBr` (saving a backtracking point if
    /// necessary) and eventually returns the new `ReturnValue` representing the
    /// return value of the function (when it reaches the end of the function), or
    /// `Ok(None)` if no possible paths were found.
    fn symex_condbr(&mut self, condbr: &'p terminator::CondBr) -> Result<Option<ReturnValue<B::BV>>> {
        debug!("Symexing condbr {:?}", condbr);
        let btorcond = self.state.operand_to_bv(&condbr.condition)?;
        let true_feasible = self.state.sat_with_extra_constraints(std::iter::once(&btorcond))?;
        let false_feasible = self.state.sat_with_extra_constraints(std::iter::once(&btorcond.not()))?;
        if true_feasible && false_feasible {
            // for now we choose to explore true first, and backtrack to false if necessary
            self.state.save_backtracking_point(condbr.false_dest.clone(), btorcond.not());
            btorcond.assert()?;
            self.state.cur_loc.bbname = condbr.true_dest.clone();
            self.symex_from_cur_loc_through_end_of_function()
        } else if true_feasible {
            btorcond.assert()?;  // unnecessary, but may help Boolector more than it hurts?
            self.state.cur_loc.bbname = condbr.true_dest.clone();
            self.symex_from_cur_loc_through_end_of_function()
        } else if false_feasible {
            btorcond.not().assert()?;  // unnecessary, but may help Boolector more than it hurts?
            self.state.cur_loc.bbname = condbr.false_dest.clone();
            self.symex_from_cur_loc_through_end_of_function()
        } else {
            self.backtrack_and_continue()
        }
    }

    /// Continues to the target(s) of the `Switch` (saving backtracking points if
    /// necessary) and eventually returns the new `ReturnValue` representing the
    /// return value of the function (when it reaches the end of the function), or
    /// `Ok(None)` if no possible paths were found.
    fn symex_switch(&mut self, switch: &'p terminator::Switch) -> Result<Option<ReturnValue<B::BV>>> {
        debug!("Symexing switch {:?}", switch);
        let switchval = self.state.operand_to_bv(&switch.operand)?;
        let dests = switch.dests
            .iter()
            .map(|(c,n)| {
                self.state.const_to_bv(c)
                    .map(|c| (c,n))
            })
            .collect::<Result<Vec<(B::BV, &Name)>>>()?;
        let feasible_dests: Vec<_> = dests.iter()
            .map(|(c,n)| {
                self.state.bvs_can_be_equal(&c, &switchval)
                    .and_then(|b| match b {
                        Some(b) => Ok((c,*n,b)),
                        None => Err(Error::Unsat),
                    })
            })
            .collect::<Result<Vec<(&B::BV, &Name, bool)>>>()?
            .into_iter()
            .filter(|(_,_,b)| *b)
            .map(|(c,n,_)| (c,n))
            .collect::<Vec<(&B::BV, &Name)>>();
        if feasible_dests.is_empty() {
            // none of the dests are feasible, we will always end up in the default dest
            self.state.cur_loc.bbname = switch.default_dest.clone();
            self.symex_from_cur_loc_through_end_of_function()
        } else {
            // make backtracking points for all but the first destination
            for (val, name) in feasible_dests.iter().skip(1) {
                self.state.save_backtracking_point((*name).clone(), val._eq(&switchval));
            }
            // if the default dest is feasible, make a backtracking point for it
            let default_dest_constraint = dests.iter()
                .map(|(c,_)| c._eq(&switchval).not())
                .reduce(|a,b| a.and(&b))
                .unwrap_or_else(|| B::BV::from_bool(self.state.solver.clone(), true));  // if `dests` was empty, that's weird, but the default dest is definitely feasible
            if self.state.sat_with_extra_constraints(std::iter::once(&default_dest_constraint))? {
                self.state.save_backtracking_point(switch.default_dest.clone(), default_dest_constraint);
            }
            // follow the first destination
            let (val, name) = &feasible_dests[0];
            val._eq(&switchval).assert()?;  // unnecessary, but may help Boolector more than it hurts?
            self.state.cur_loc.bbname = (*name).clone();
            self.symex_from_cur_loc_through_end_of_function()
        }
    }

    fn symex_phi(&mut self, phi: &'p instruction::Phi) -> Result<()> {
        debug!("Symexing phi {:?}", phi);
        let path = self.state.get_path();
        let prev_bb = match path.len() {
            0|1 => panic!("not yet implemented: starting in a block with Phi instructions. or error: didn't expect a Phi in function entry block"),
            len => &path[len - 2].bbname,  // the last entry is our current block, so we want the one before
        };
        let chosen_value = phi.incoming_values.iter()
            .find(|&(_, bbname)| bbname == prev_bb)
            .map(|(op, _)| op)
            .ok_or_else(|| Error::OtherError(format!("Failed to find a Phi member matching previous BasicBlock. Phi incoming_values are {:?} but we were looking for {:?}", phi.incoming_values, prev_bb)))?;
        self.state.record_bv_result(phi, self.state.operand_to_bv(&chosen_value)?)
    }

    fn symex_select(&mut self, select: &'p instruction::Select) -> Result<()> {
        debug!("Symexing select {:?}", select);
        let truetype = select.true_value.get_type();
        let falsetype = select.false_value.get_type();
        if truetype != falsetype {
            return Err(Error::MalformedInstruction(format!("Expected Select operands to have identical type, but they have types {:?} and {:?}", truetype, falsetype)));
        }
        let optype = truetype;
        match select.condition.get_type() {
            Type::IntegerType { bits } if bits == 1 => {
                let btorcond = self.state.operand_to_bv(&select.condition)?;
                let btortrueval = self.state.operand_to_bv(&select.true_value)?;
                let btorfalseval = self.state.operand_to_bv(&select.false_value)?;
                let true_feasible = self.state.sat_with_extra_constraints(std::iter::once(&btorcond))?;
                let false_feasible = self.state.sat_with_extra_constraints(std::iter::once(&btorcond.not()))?;
                if true_feasible && false_feasible {
                    self.state.record_bv_result(select, btorcond.cond_bv(&btortrueval, &btorfalseval))
                } else if true_feasible {
                    btorcond.assert()?;  // unnecessary, but may help Boolector more than it hurts?
                    self.state.record_bv_result(select, btortrueval)
                } else if false_feasible {
                    btorcond.not().assert()?;  // unnecessary, but may help Boolector more than it hurts?
                    self.state.record_bv_result(select, btorfalseval)
                } else {
                    // this path is unsat
                    Err(Error::Unsat)
                }
            },
            Type::VectorType { element_type, num_elements } => {
                match *element_type {
                    Type::IntegerType { bits: 1 } => {},
                    ty => return Err(Error::MalformedInstruction(format!("Expected Select vector condition to be vector of i1, but got vector of {:?}", ty))),
                };
                let el_size = match optype {
                    Type::VectorType { element_type: op_el_type, num_elements: op_num_els } => {
                        if num_elements != op_num_els {
                            return Err(Error::MalformedInstruction(format!("Select condition is a vector of {} elements but operands are vectors with {} elements", num_elements, op_num_els)));
                        }
                        size(&op_el_type) as u32
                    },
                    _ => return Err(Error::MalformedInstruction(format!("Expected Select with vector condition to have vector operands, but operands are of type {:?}", optype))),
                };
                let condvec = self.state.operand_to_bv(&select.condition)?;
                let truevec = self.state.operand_to_bv(&select.true_value)?;
                let falsevec = self.state.operand_to_bv(&select.false_value)?;
                let final_bv = (0 .. num_elements as u32)
                    .map(|idx| {
                        let bit = condvec.slice(idx, idx);
                        bit.cond_bv(
                            &truevec.slice((idx+1) * el_size - 1, idx * el_size),
                            &falsevec.slice((idx+1) * el_size - 1, idx * el_size),
                        )
                    })
                    .reduce(|a,b| b.concat(&a)).ok_or_else(|| Error::MalformedInstruction("Select with vectors of 0 elements".to_owned()))?;
                self.state.record_bv_result(select, final_bv)
            }
            ty => Err(Error::MalformedInstruction(format!("Expected select condition to be i1 or vector of i1, but got {:?}", ty))),
        }
    }
}

// Built-in "hooks" for LLVM intrinsics

fn symex_memset<'p, B: Backend>(state: &mut State<'p, B>, call: &'p instruction::Call) -> Result<()> {
    assert_eq!(call.arguments.len(), 4);
    let addr = &call.arguments[0].0;
    let val = &call.arguments[1].0;
    let num_bytes = &call.arguments[2].0;
    assert_eq!(addr.get_type(), Type::pointer_to(Type::i8()));

    let addr = state.operand_to_bv(&addr)?;
    let val = {
        let mut val = state.operand_to_bv(&val)?;
        if val.get_width() > 8 {
            // some memset declarations have a larger type here, but it's still intended to be a byte value; we ignore any upper bits
            val = val.slice(7, 0);
        }
        val
    };

    let num_bytes = state.operand_to_bv(num_bytes)?;
    let num_bytes = match state.get_possible_solutions_for_bv(&num_bytes, 1)? {
        PossibleSolutions::Exactly(v) => v.iter().next().ok_or(Error::Unsat)?.as_u64().unwrap(),
        PossibleSolutions::AtLeast(v) => {
            let num_bytes_concrete = match state.config.concretize_memcpy_lengths {
                Concretize::Arbitrary => v.iter().next().unwrap().as_u64().unwrap(),
                Concretize::Minimum => solver_utils::min_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap(),
                Concretize::Maximum => solver_utils::max_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap(),
                Concretize::Prefer(val, _) => {
                    let val_as_bv = B::BV::from_u64(state.solver.clone(), val, num_bytes.get_width());
                    if state.bvs_can_be_equal(&num_bytes, &val_as_bv)?.ok_or(Error::Unsat)? {
                        val
                    } else {
                        return Err(Error::UnsupportedInstruction("not implemented yet: memset with non-constant num_bytes, Concretize::Prefer, and needing to execute the fallback path".to_owned()));
                    }
                },
                Concretize::Symbolic => {
                    // In this case we just do the entire write here and return
                    let max_num_bytes = solver_utils::max_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap();
                    let mut addr = addr;
                    let mut bytes_written = B::BV::zero(state.solver.clone(), num_bytes.get_width());
                    for _ in 0 ..= max_num_bytes {
                        let old_val = state.read(&addr, 8)?;
                        let should_write = num_bytes.ugt(&bytes_written);
                        state.write(&addr, should_write.cond_bv(&val, &old_val))?;
                        addr = addr.inc();
                        bytes_written = bytes_written.inc();
                    }
                    return Ok(());
                }
            };
            num_bytes._eq(&B::BV::from_u64(state.solver.clone(), num_bytes_concrete, num_bytes.get_width())).assert()?;
            num_bytes_concrete
        }
    };

    // If we're still here, we picked a single concrete value for num_bytes
    if num_bytes == 0 {
        debug!("Ignoring a memset of 0 num_bytes");
    } else {
        debug!("Processing a memset of {} bytes", num_bytes);
        // Do the operation as just one large write; let the memory choose the most efficient way to implement that.
        assert_eq!(val.get_width(), 8);
        let big_val = if state.bvs_must_be_equal(&val, &B::BV::zero(state.solver.clone(), 8))?.ok_or(Error::Unsat)? {
            // optimize this special case
            B::BV::zero(state.solver.clone(), 8 * u32::try_from(num_bytes).map_err(|e| Error::OtherError(format!("memset too big: {} bytes (error: {})", num_bytes, e)))?)
        } else if state.bvs_must_be_equal(&val, &B::BV::ones(state.solver.clone(), 8))?.ok_or(Error::Unsat)? {
            // optimize this special case
            B::BV::ones(state.solver.clone(), 8 * u32::try_from(num_bytes).map_err(|e| Error::OtherError(format!("memset too big: {} bytes (error: {})", num_bytes, e)))?)
        } else {
            std::iter::repeat(val).take(num_bytes as usize).reduce(|a,b| a.concat(&b)).unwrap()
        };
        state.write(&addr, big_val)?;
    }

    // if the call should return a pointer, it returns `addr`. If it's void-typed, that's fine too.
    match call.get_type() {
       Type::VoidType => Ok(()),
       Type::PointerType { .. } => {
            // can't quite use `state.record_bv_result(call, addr)?` because Call is not HasResult
            state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), addr)?;
            Ok(())
       },
       ty => Err(Error::OtherError(format!("Unexpected return type for a memset: {:?}", ty))),
    }
}

fn symex_memcpy<'p, B: Backend>(state: &mut State<'p, B>, call: &'p instruction::Call) -> Result<()> {
    let dest = &call.arguments[0].0;
    let src = &call.arguments[1].0;
    let num_bytes = &call.arguments[2].0;
    assert_eq!(dest.get_type(), Type::pointer_to(Type::i8()));
    assert_eq!(src.get_type(), Type::pointer_to(Type::i8()));

    let dest = state.operand_to_bv(&dest)?;
    let src = state.operand_to_bv(&src)?;

    let num_bytes = state.operand_to_bv(num_bytes)?;
    let num_bytes = match state.get_possible_solutions_for_bv(&num_bytes, 1)? {
        PossibleSolutions::Exactly(v) => v.iter().next().ok_or(Error::Unsat)?.as_u64().unwrap(),
        PossibleSolutions::AtLeast(v) => {
            let num_bytes_concrete = match state.config.concretize_memcpy_lengths {
                Concretize::Arbitrary => v.iter().next().unwrap().as_u64().unwrap(),
                Concretize::Minimum => solver_utils::min_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap(),
                Concretize::Maximum => solver_utils::max_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap(),
                Concretize::Prefer(val, _) => {
                    let val_as_bv = B::BV::from_u64(state.solver.clone(), val, num_bytes.get_width());
                    if state.bvs_can_be_equal(&num_bytes, &val_as_bv)?.ok_or(Error::Unsat)? {
                        val
                    } else {
                        return Err(Error::UnsupportedInstruction("not implemented yet: memcpy or memmove with non-constant num_bytes, Concretize::Prefer, and needing to execute the fallback path".to_owned()));
                    }
                },
                Concretize::Symbolic => {
                    // In this case we just do the entire write here and return
                    let max_num_bytes = solver_utils::max_possible_solution_for_bv(state.solver.clone(), &num_bytes)?.unwrap();
                    debug!("Processing a memcpy with symbolic num_bytes, up to {}", max_num_bytes);
                    let mut src_addr = src;
                    let mut dest_addr = dest;
                    let mut bytes_written = B::BV::zero(state.solver.clone(), num_bytes.get_width());
                    for _ in 0 ..= max_num_bytes {
                        let src_val = state.read(&src_addr, 8)?;
                        let dst_val = state.read(&dest_addr, 8)?;
                        let should_write = num_bytes.ugt(&bytes_written);
                        state.write(&dest_addr, should_write.cond_bv(&src_val, &dst_val))?;
                        src_addr = src_addr.inc();
                        dest_addr = dest_addr.inc();
                        bytes_written = bytes_written.inc();
                    }
                    return Ok(());
                }
            };
            num_bytes._eq(&B::BV::from_u64(state.solver.clone(), num_bytes_concrete, num_bytes.get_width())).assert()?;
            num_bytes_concrete
        },
    };

    // If we're still here, we picked a single concrete value for num_bytes
    if num_bytes == 0 {
        debug!("Ignoring a memcpy or memmove of 0 num_bytes");
    } else {
        debug!("Processing memcpy of {} bytes", num_bytes);
        // Do the operation as just one large read and one large write; let the memory choose the most efficient way to implement these.
        let val = state.read(&src, num_bytes as u32 * 8)?;
        state.write(&dest, val)?;
    }

    // if the call should return a pointer, it returns `dest`. If it's void-typed, that's fine too.
    match call.get_type() {
       Type::VoidType => Ok(()),
       Type::PointerType { .. } => {
            // can't quite use `state.record_bv_result(call, dest)?` because Call is not HasResult
            state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), dest)?;
            Ok(())
       },
       ty => Err(Error::OtherError(format!("Unexpected return type for a memcpy or memmove: {:?}", ty))),
    }
}

fn symex_objectsize<'p, B: Backend>(state: &mut State<'p, B>, call: &'p instruction::Call) -> Result<()> {
    // We have no way of tracking in-memory types, so we can't provide the
    // intended answers for this intrinsic. Instead, we just always return
    // 'unknown', as this is valid behavior according to the LLVM spec.
    let arg1 = state.operand_to_bv(&call.arguments[1].0)?;
    let width = size(&call.get_type());
    let zero = B::BV::zero(state.solver.clone(), width as u32);
    let minusone = B::BV::ones(state.solver.clone(), width as u32);
    state.assign_bv_to_name(call.dest.as_ref().unwrap().clone(), arg1.cond_bv(&zero, &minusone))
}

#[cfg(test)]
mod tests {
    //! These tests check that the correct set of _paths_ are generated for various
    //! functions. In contrast, the integration tests in the tests/ folder test for
    //! specific solutions for function parameters and return values.

    use llvm_ir::*;
    use super::*;

    fn init_logging() {
        // capture log messages with test harness
        let _ = env_logger::builder().is_test(true).try_init();
    }

    type Path = Vec<PathEntry>;

    fn path_from_bbnames(modname: &str, funcname: &str, bbnames: impl IntoIterator<Item = Name>) -> Path {
        let mut vec = vec![];
        for bbname in bbnames {
            vec.push(PathEntry { modname: modname.to_owned(), funcname: funcname.to_owned(), bbname });
        }
        vec
    }

    fn path_from_bbnums(modname: &str, funcname: &str, bbnums: impl IntoIterator<Item = usize>) -> Path {
        path_from_bbnames(modname, funcname, bbnums.into_iter().map(Name::from))
    }

    fn path_from_func_and_bbname_pairs<'a>(modname: &str, pairs: impl IntoIterator<Item = (&'a str, Name)>) -> Path {
        let mut vec = vec![];
        for (funcname, bbname) in pairs {
            vec.push(PathEntry { modname: modname.to_owned(), funcname: funcname.to_owned(), bbname });
        }
        vec
    }

    fn path_from_func_and_bbnum_pairs<'a>(modname: &str, pairs: impl IntoIterator<Item = (&'a str, usize)>) -> Path {
        path_from_func_and_bbname_pairs(modname, pairs.into_iter().map(|(f, num)| (f, Name::from(num))))
    }

    /// Build a path from (modname, funcname, bbnum) triples
    fn path_from_triples<'a>(triples: impl IntoIterator<Item = (&'a str, &'a str, usize)>) -> Path {
        let mut vec = vec![];
        for (modname, funcname, bbnum) in triples {
            vec.push(PathEntry { modname: modname.to_owned(), funcname: funcname.to_owned(), bbname: Name::from(bbnum) });
        }
        vec
    }

    /// Iterator over the paths through a function
    struct PathIterator<'p, B: Backend> {
        em: ExecutionManager<'p, B>,
    }

    impl<'p, B: Backend> PathIterator<'p, B> {
        /// For argument descriptions, see notes on `symex_function`
        pub fn new(
            funcname: &str,
            project: &'p Project,
            config: Config<'p, B>,
        ) -> Self {
            Self { em: symex_function(funcname, project, config) }
        }
    }

    impl<'p, B: Backend> Iterator for PathIterator<'p, B> where B: 'p {
        type Item = Path;

        fn next(&mut self) -> Option<Self::Item> {
            self.em.next().map(|_| self.em.state().get_path().clone())
        }
    }

    #[test]
    fn one_block() {
        let modname = "tests/bcfiles/basic.bc";
        let funcname = "one_arg";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = PathIterator::<BtorBackend>::new(funcname, &proj, config).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn two_paths() {
        let modname = "tests/bcfiles/basic.bc";
        let funcname = "conditional_true";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![2, 4, 12]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![2, 8, 12]));
        assert_eq!(paths.len(), 2);  // ensure there are no more paths
    }

    #[test]
    fn four_paths() {
        let modname = "tests/bcfiles/basic.bc";
        let funcname = "conditional_nozero";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![2, 4, 6, 14]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![2, 4, 8, 10, 14]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![2, 4, 8, 12, 14]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![2, 14]));
        assert_eq!(paths.len(), 4);  // ensure there are no more paths
    }

    #[test]
    fn switch() {
        let modname = "tests/bcfiles/basic.bc";
        let funcname = "has_switch";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![2, 4, 14]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![2, 5, 14]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![2, 7, 14]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![2, 10, 14]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![2, 11, 14]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![2, 12, 14]));
        assert_eq!(paths[6], path_from_bbnums(modname, funcname, vec![2, 14]));
        assert_eq!(paths.len(), 7);  // ensure there are no more paths

    }

    #[test]
    fn while_loop() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "while_loop";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 6, 6, 6, 6, 6, 12]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 6, 6, 6, 6, 12]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 6, 6, 6, 12]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 6, 6, 12]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 6, 12]));
        assert_eq!(paths.len(), 5);  // ensure there are no more paths
    }

    #[test]
    fn for_loop() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "for_loop";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 6]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 9, 6]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 9, 9, 6]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 9, 9, 9, 6]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 9, 9, 9, 9, 6]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![1, 9, 9, 9, 9, 9, 6]));
        assert_eq!(paths.len(), 6);  // ensure there are no more paths
    }

    #[test]
    fn loop_more_blocks() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "loop_zero_iterations";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 5, 8, 18]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 5, 11, 8, 18]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 5, 11, 11, 8, 18]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 5, 11, 11, 11, 8, 18]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 5, 11, 11, 11, 11, 8, 18]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![1, 5, 11, 11, 11, 11, 11, 8, 18]));
        assert_eq!(paths[6], path_from_bbnums(modname, funcname, vec![1, 18]));
        assert_eq!(paths.len(), 7);  // ensure there are no more paths
    }

    #[test]
    fn loop_more_blocks_in_body() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "loop_with_cond";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 6, 13, 16,
                                                                         6, 10, 16,
                                                                         6, 10, 16,
                                                                         6, 13, 16,
                                                                         6, 10, 16, 20]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 6, 13, 16,
                                                                         6, 10, 16,
                                                                         6, 10, 16,
                                                                         6, 13, 16, 20]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 6, 13, 16,
                                                                         6, 10, 16,
                                                                         6, 10, 16, 20]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 6, 13, 16,
                                                                         6, 10, 16, 20]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 6, 13, 16, 20]));
        assert_eq!(paths.len(), 5);  // ensure there are no more paths
    }

    #[test]
    fn two_loops() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "sum_of_array";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 30, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 4,  4,  4,  4,  4,  4,  4,  4,  4,  4,
                                                                         11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 9]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn nested_loop() {
        let modname = "tests/bcfiles/loop.bc";
        let funcname = "nested_loop";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 30, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 7]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 7]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 5, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
                                                                     10, 7]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 7]));
        assert_eq!(paths.len(), 4);  // ensure there are no more paths
    }

    #[test]
    fn simple_call() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "simple_caller";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(&modname, vec![
            ("simple_caller", 1),
            ("simple_callee", 2),
            ("simple_caller", 1),
        ]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn cross_module_simple_call() {
        let callee_modname = "tests/bcfiles/call.bc";
        let caller_modname = "tests/bcfiles/crossmod.bc";
        let funcname = "cross_module_simple_caller";
        init_logging();
        let proj = Project::from_bc_paths(vec![callee_modname, caller_modname].into_iter().map(std::path::Path::new))
            .unwrap_or_else(|e| panic!("Failed to parse modules: {}", e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_triples(vec![
            (caller_modname, "cross_module_simple_caller", 1),
            (callee_modname, "simple_callee", 2),
            (caller_modname, "cross_module_simple_caller", 1),
        ]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn conditional_call() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "conditional_caller";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("conditional_caller", 2),
            ("conditional_caller", 4),
            ("simple_callee", 2),
            ("conditional_caller", 4),
            ("conditional_caller", 8),
        ]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![2, 6, 8]));
        assert_eq!(paths.len(), 2);  // ensure there are no more paths
    }

    #[test]
    fn call_twice() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "twice_caller";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("twice_caller", 1),
            ("simple_callee", 2),
            ("twice_caller", 1),
            ("simple_callee", 2),
            ("twice_caller", 1),
        ]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn cross_module_call_twice() {
        let callee_modname = "tests/bcfiles/call.bc";
        let caller_modname = "tests/bcfiles/crossmod.bc";
        let funcname = "cross_module_twice_caller";
        init_logging();
        let proj = Project::from_bc_paths(vec![callee_modname, caller_modname].into_iter().map(std::path::Path::new))
            .unwrap_or_else(|e| panic!("Failed to parse modules: {}", e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_triples(vec![
            (caller_modname, "cross_module_twice_caller", 1),
            (callee_modname, "simple_callee", 2),
            (caller_modname, "cross_module_twice_caller", 1),
            (callee_modname, "simple_callee", 2),
            (caller_modname, "cross_module_twice_caller", 1),
        ]));
        assert_eq!(paths.len(), 1);  // enusre there are no more paths
    }

    #[test]
    fn nested_call() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "nested_caller";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("nested_caller", 2),
            ("simple_caller", 1),
            ("simple_callee", 2),
            ("simple_caller", 1),
            ("nested_caller", 2),
        ]));
        assert_eq!(paths.len(), 1);  // ensure there are no more paths
    }

    #[test]
    fn cross_module_nested_near_call() {
        let callee_modname = "tests/bcfiles/call.bc";
        let caller_modname = "tests/bcfiles/crossmod.bc";
        let funcname = "cross_module_nested_near_caller";
        init_logging();
        let proj = Project::from_bc_paths(vec![callee_modname, caller_modname].into_iter().map(std::path::Path::new))
            .unwrap_or_else(|e| panic!("Failed to parse modules: {}", e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_triples(vec![
            (caller_modname, "cross_module_nested_near_caller", 2),
            (caller_modname, "cross_module_simple_caller", 1),
            (callee_modname, "simple_callee", 2),
            (caller_modname, "cross_module_simple_caller", 1),
            (caller_modname, "cross_module_nested_near_caller", 2),
        ]));
        assert_eq!(paths.len(), 1);  // enusre there are no more paths
    }

    #[test]
    fn cross_module_nested_far_call() {
        let callee_modname = "tests/bcfiles/call.bc";
        let caller_modname = "tests/bcfiles/crossmod.bc";
        let funcname = "cross_module_nested_far_caller";
        init_logging();
        let proj = Project::from_bc_paths(vec![callee_modname, caller_modname].into_iter().map(std::path::Path::new))
            .unwrap_or_else(|e| panic!("Failed to parse modules: {}", e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_triples(vec![
            (caller_modname, "cross_module_nested_far_caller", 2),
            (callee_modname, "simple_caller", 1),
            (callee_modname, "simple_callee", 2),
            (callee_modname, "simple_caller", 1),
            (caller_modname, "cross_module_nested_far_caller", 2),
        ]));
        assert_eq!(paths.len(), 1);  // enusre there are no more paths
    }

    #[test]
    fn call_of_loop() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "caller_of_loop";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths[1], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 13),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths[2], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths[3], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths[4], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths[5], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_of_loop", 1),
            ("callee_with_loop", 2),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 13),
            ("callee_with_loop", 9),
            ("caller_of_loop", 1),
        ]));
        assert_eq!(paths.len(), 6);  // ensure there are no more paths
    }

    #[test]
    fn call_in_loop() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "caller_with_loop";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 3, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_with_loop", 1),
            ("caller_with_loop", 8),
        ]));
        assert_eq!(paths[1], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_with_loop", 1),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 6),
            ("caller_with_loop", 8),
        ]));
        assert_eq!(paths[2], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_with_loop", 1),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 6),
            ("caller_with_loop", 8),
        ]));
        assert_eq!(paths[3], path_from_func_and_bbnum_pairs(modname, vec![
            ("caller_with_loop", 1),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 10),
            ("simple_callee", 2),
            ("caller_with_loop", 10),
            ("caller_with_loop", 6),
            ("caller_with_loop", 8),
        ]));
        assert_eq!(paths.len(), 4);  // ensure there are no more paths
    }

    #[test]
    fn recursive_simple() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "recursive_simple";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 5, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 4, 9, 6, 6, 6, 6]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 9, 6, 6, 6, 6]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 4, 9, 6, 6, 6]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 4, 6, 1, 9, 6, 6, 6]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 4, 9, 6, 6]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 6, 1, 9, 6, 6]));
        assert_eq!(paths[6], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 4, 9, 6]));
        assert_eq!(paths[7], path_from_bbnums(modname, funcname, vec![1, 4, 6, 1, 9, 6]));
        assert_eq!(paths[8], path_from_bbnums(modname, funcname, vec![1, 4, 9]));
        assert_eq!(paths[9], path_from_bbnums(modname, funcname, vec![1, 9]));
        assert_eq!(paths.len(), 10);  // ensure there are no more paths
    }

    #[test]
    fn recursive_double() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "recursive_double";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 4, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 4, 6, 8, 1, 4, 6, 8, 1, 4, 6, 8, 1, 4, 20, 8, 8, 8]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 4, 6, 8, 1, 4, 6, 8, 1, 4, 20, 8, 8]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 4, 6, 8, 1, 4, 20, 8]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 4, 6, 12, 14, 1, 4, 6, 8, 1, 4, 6, 8, 1, 4, 20, 8, 8, 14]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 4, 6, 12, 14, 1, 4, 6, 8, 1, 4, 20, 8, 14]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![1, 4, 6, 12, 14, 1, 4, 6, 12, 18, 20, 14]));
        assert_eq!(paths[6], path_from_bbnums(modname, funcname, vec![1, 4, 6, 12, 14, 1, 4, 20, 14]));
        assert_eq!(paths[7], path_from_bbnums(modname, funcname, vec![1, 4, 6, 12, 18, 20]));
        assert_eq!(paths[8], path_from_bbnums(modname, funcname, vec![1, 4, 20]));
        assert_eq!(paths[9], path_from_bbnums(modname, funcname, vec![1, 20]));
        assert_eq!(paths.len(), 10);  // ensure there are no more paths
    }

    #[test]
    fn recursive_not_tail() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "recursive_not_tail";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 3, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_bbnums(modname, funcname, vec![1, 3, 15]));
        assert_eq!(paths[1], path_from_bbnums(modname, funcname, vec![1, 5, 1, 3, 15, 5, 10, 15]));
        assert_eq!(paths[2], path_from_bbnums(modname, funcname, vec![1, 5, 1, 3, 15, 5, 12, 15]));
        assert_eq!(paths[3], path_from_bbnums(modname, funcname, vec![1, 5, 1, 5, 1, 3, 15, 5, 10, 15, 5, 10, 15]));
        assert_eq!(paths[4], path_from_bbnums(modname, funcname, vec![1, 5, 1, 5, 1, 3, 15, 5, 10, 15, 5, 12, 15]));
        assert_eq!(paths[5], path_from_bbnums(modname, funcname, vec![1, 5, 1, 5, 1, 3, 15, 5, 12, 15, 5, 10, 15]));
        assert_eq!(paths[6], path_from_bbnums(modname, funcname, vec![1, 5, 1, 5, 1, 3, 15, 5, 12, 15, 5, 12, 15]));
        assert_eq!(paths.len(), 7);  // ensure there are no more paths
    }

    #[test]
    fn recursive_and_normal_call() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "recursive_and_normal_caller";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 3, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 7),
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 7),
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 10),
            ("recursive_and_normal_caller", 7),
            ("recursive_and_normal_caller", 7),
        ]));
        assert_eq!(paths[1], path_from_func_and_bbnum_pairs(modname, vec![
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 7),
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 10),
            ("recursive_and_normal_caller", 7),
        ]));
        assert_eq!(paths[2], path_from_func_and_bbnum_pairs(modname, vec![
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 7),
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 10),
            ("recursive_and_normal_caller", 7),
        ]));
        assert_eq!(paths[3], path_from_func_and_bbnum_pairs(modname, vec![
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 3),
            ("simple_callee", 2),
            ("recursive_and_normal_caller", 3),
            ("recursive_and_normal_caller", 10),
        ]));
        assert_eq!(paths[4], path_from_func_and_bbnum_pairs(modname, vec![
            ("recursive_and_normal_caller", 1),
            ("recursive_and_normal_caller", 10),
        ]));
        assert_eq!(paths.len(), 5);  // ensure there are no more paths
    }

    #[test]
    fn mutually_recursive_functions() {
        let modname = "tests/bcfiles/call.bc";
        let funcname = "mutually_recursive_a";
        init_logging();
        let proj = Project::from_bc_path(&std::path::Path::new(modname))
            .unwrap_or_else(|e| panic!("Failed to parse module {:?}: {}", modname, e));
        let config = Config { loop_bound: 3, ..Config::default() };
        let paths: Vec<Path> = itertools::sorted(PathIterator::<BtorBackend>::new(funcname, &proj, config)).collect();
        assert_eq!(paths[0], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths[1], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths[2], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths[3], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 7),
            ("mutually_recursive_b", 3),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths[4], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_b", 1),
            ("mutually_recursive_b", 7),
            ("mutually_recursive_a", 3),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths[5], path_from_func_and_bbnum_pairs(modname, vec![
            ("mutually_recursive_a", 1),
            ("mutually_recursive_a", 7),
        ]));
        assert_eq!(paths.len(), 6);  // ensure there are no more paths
    }
}

/// Much of this file is copied from the main thing I wrote to prevent circular deps.
/// TODO: Reorganize this so there isn't code duplication.
/// TODO: Make use of this dependent on config so stock haybale can also be used.
/// TODO: Move MIR files into memory once at start so rebuilding during execution is okay
/// TODO: One potential issue with the logic here is that finding the longest path for any input
/// is not the same as the longest path with the current constraints. So here we are finding the
/// longest possible path for any input, then assuming that is also the longest path with current
/// constraints, which might lead to finding a path that is not the longest path. Potential fixes
/// include a) what I have always wanted, which is treating trait object calls as branches and
/// evaluating all paths with current constraints or b) something similar but short of that where
/// all paths are evaluated with current constraints in a new haybale run, then we pass the
/// concrete function once we have found the longest.
/// HUDSON 11/8/22: I don't think the above note is correct, errors should only be pessimistic.
use crate::backend::*;
use crate::*;
use std::collections::HashSet;
use std::result::Result;
use std::string::String;
use std::time::Instant;

/// Given a function name and project/configuration, returns the longest path
/// (in llvm IR "instructions") through that function, as well as a copy of the `State` of
/// the execution manager at the conclusion of symbolically executing that path. Ties
/// are broken at random.
pub fn find_longest_path<'p, B: Backend>(
    funcname: &str,
    project: &'p Project,
    config: Config<'p, B>,
    time_results: bool,
) -> Result<(usize, State<'p, B>), String> {
    let mut em: ExecutionManager<B> = symex_function(funcname, project, config, None).unwrap();
    let mut longest_path_len = 0;
    let mut longest_path_state = None;
    let mut i = 0;
    loop {
        let start = Instant::now();
        match em.next() {
            Some(res) => match res {
                Ok(_) => {
                    if time_results {
                        print!(
                            "Call to next() #{} completed in {} seconds ",
                            i,
                            start.elapsed().as_secs()
                        );
                    }
                },
                Err(Error::UnreachableInstruction) => {
                    // Rust inserts unreachable assertions along paths that it knows will not be
                    // reachable unless we violate Rust's memory/type safety. LLVM IR on its own
                    // does not have enough information to know these paths will never be
                    // reachable, so sometimes haybale will attempt to execute unreachable
                    // instructions. We simply have to ignore all paths containing these
                    // instructions.
                    i += 1;
                    continue;
                },
                Err(Error::SolverError(e)) => {
                    if !e.contains("timed out") {
                        println!("Solver error, not a timeout.");
                        return Err(em
                            .state()
                            .full_error_message_with_context(Error::SolverError(e)));
                    } else {
                        println!("{}", e);
                        if em.retry_ongoing {
                            panic!("Double timeout");
                        }
                    }
                    println!("Solver timeout detected! Attempting to loosen constraints.");
                    // This is usually a timeout, so for now we will assume this is always a
                    // timeout. My approach to solver timeouts is:
                    //
                    // 1. Find the enclosing function of the current location when we timed out
                    //
                    let state = em.mut_state();
                    println!(
                        "Location of timeout: {}",
                        state.cur_loc.to_string_no_module()
                    );
                    let callsite = &state.stack.last().unwrap().callsite;
                    //
                    // 2. Instruct Haybale that the next time we call this function, we are going
                    //    to execute it without any constraints on its inputs -- e.g. we are going
                    //    to assume that all values in memory could be anything, and all passed in
                    //    parameters could be anything.
                    //    TODO: What if this function is called in a loop? This will not push any
                    //    new backtrack points on but will lead to multiple calls..I guess we want
                    //    to keep the function unconstrained until the current backtrack point is
                    //    complete. Configured to panic internally if this happens, lets see if it
                    //    is an issue in practice.
                    //
                    state.fn_to_clear = Some(callsite.clone());
                    println!("fn_to_clear: {:?}", state.fn_to_clear);
                    //
                    // 3. Find where in the failing path this function was last called, and then find
                    //    the backtracking point immediately preceding this call
                    //
                    let restart_point = state.last_backtrack_point.take().unwrap();
                    // Verify that the restart point is not in the same call frame as the point of
                    // failure, if it is backtracking will not help us because the constraints will
                    // be unchanged. TODO improve this to not panic and instead print useful info.
                    assert!(&(restart_point.stack.last().unwrap().callsite) != callsite);
                    println!("restart point: {:?}", restart_point.loc);
                    state.solver.push(1); // Solver level needs to be in sync with backtrack queue
                    state.backtrack_points.borrow_mut().push(restart_point);
                    em.retry_ongoing = true;
                    // now next call to next() should resume from restart_point!
                    continue;
                },
                Err(e) => {
                    println!(
                        "Call to next() # {} failed after {} seconds",
                        i,
                        start.elapsed().as_secs()
                    );
                    println!(
                        "Failed while executing instruction in {}",
                        em.state().cur_loc.func.name
                    );
                    println!("Pretty path source: {}", em.state().pretty_path_source());
                    return Err(em.state().full_error_message_with_context(e));
                },
            },
            None => break,
        }
        if em.retry_ongoing {
            println!("RETRY SUCCESSFUL!!!");
            em.retry_ongoing = false; // we completed a path
        }
        i += 1;
        let state = em.state();
        let path = state.get_path();
        let len = crate::get_path_length(path);
        if len > longest_path_len {
            longest_path_len = len;
            longest_path_state = Some(state.clone());
        }
    }
    longest_path_state.map_or(Err("No Paths found".to_string()), |state| {
        Ok((longest_path_len, state))
    })
}

pub enum DynDispatchLookupError {
    NoImplementationsFound,
}

/// Return the longest possible path for a given method call on a trait object.
pub(crate) fn longest_path_dyn_dispatch<'p, B: Backend>(
    project: &'p Project,
    config: Config<'p, B>,
    method_name: &str,
    trait_name: &str,
) -> Result<&'p str, DynDispatchLookupError> {
    // First, check if we have already done a lookup for this trait method. For now use a global
    // for ease, though a field on the project would work better (but would require adding lots
    // of lifetime annotations).
    let map = project.trait_obj_map.try_lock().unwrap();
    let lookup = map.get(&(method_name.to_string(), trait_name.to_string()));
    match lookup {
        Some(s) => {
            //println!("Longest lookup match!");
            return Ok(project.get_func_by_name(s).unwrap().0.name.as_str());
        },
        _ => {},
    }
    drop(map); //unlock mutex, this function can be called by itself

    let matches = project.all_functions().filter(|(f, _m)| {
        let demangled = rustc_demangle::try_demangle(&f.name);
        if demangled.is_err() {
            false
        } else {
            let demangled = demangled.unwrap().to_string();
            demangled.contains(method_name) && demangled.contains(trait_name)
        }
    });
    let num_matches = matches.count();
    // just filtering twice was the quickest way to get the count of matches without evaluating
    // path length for any elements. Also, only do the extra lookup for duplicates here. Otherwise
    // num_matches == 1 could happen when there are actually two concrete impls.
    let mut matches2 = project.all_functions().filter(|(f, _m)| {
        let demangled = rustc_demangle::try_demangle(&f.name);
        if demangled.is_err() {
            false
        } else {
            let demangled = demangled.unwrap().to_string();
            let fake_recursion_store = project.fake_recursion_store.try_lock().unwrap();
            demangled.contains(method_name)
                && demangled.contains(trait_name)
                && !fake_recursion_store.contains(&f.name.to_string())
            // if the fake recursion store contains this function name, we are within an
            // execution of this function which we know should not call itself.
        }
    });
    let mut longest = 0;
    let mut longest_func_name = None;
    if num_matches == 1 {
        // if num matches == 1, just return the function name without tracing it (optimization)
        longest_func_name = Some(&matches2.next().unwrap().0.name);
    } else {
        //println!("num_matches: {:?}", num_matches);
        for (f, _m) in matches2 {
            let mut under_analysis_set = project.trait_under_analysis.try_lock().unwrap();

            if under_analysis_set.contains(&f.name.to_string()) {
                // recursive invocation of concrete function for trait obj call
                // assume this particular method call is impossible.
                // Put it in the set corresponding to the trait being analyzed
                let mut detected_recursion = project.detected_recursion.try_lock().unwrap();
                let val = detected_recursion
                    .entry((trait_name.to_string(), method_name.to_string()))
                    .or_insert(HashSet::new());
                val.insert(f.name.to_string().clone());
                //println!("STORING IN detected_recursion");
                continue;
            }
            //println!("tracing {:?}", f.name);
            under_analysis_set.insert(f.name.to_string()); //store mangled name of the function we are tracing.
            drop(under_analysis_set); // unlock mutex
            if let Ok((len, _state)) = find_longest_path(&f.name, &project, config.clone(), false) {
                if len > longest {
                    longest = len;
                    longest_func_name = Some(&f.name);
                }
            }

            let mut under_analysis_set = project.trait_under_analysis.try_lock().unwrap();
            assert!(under_analysis_set.remove(&f.name.to_string())); //assert so we panic if it wasnt there, which would be an error
        }
        longest_func_name.map(|name| println!("longest match: {:?}", name));
    }

    let detected_recursion = project.detected_recursion.try_lock().unwrap();
    let skip_opt = if detected_recursion
        .get(&(trait_name.to_string(), method_name.to_string()))
        .map_or(false, |set| set.contains(longest_func_name.unwrap()))
    {
        let mut fake_recursion_store = project.fake_recursion_store.try_lock().unwrap();
        fake_recursion_store.insert(longest_func_name.unwrap().to_string());
        if longest_func_name.unwrap().contains("next") {
            //santity check, TODO: better solution
            panic!("ERROR: Iterator methods must be chainable.");
        }
        // unfortunately this optimization breaks my hack for avoiding the recursion once
        // the concrete function is returned.
        true
    } else {
        false
    };

    if !skip_opt {
        // Place the found longest match in the map to prevent repeating the work for future lookups
        longest_func_name.map(|name| {
            let mut map = project.trait_obj_map.try_lock().unwrap();
            map.insert(
                (method_name.to_string(), trait_name.to_string()),
                name.to_string(),
            );
        });
    } else {
        //println!("Skipping save optimization, executing concrete function with recursion");
    }

    if let Some(name) = longest_func_name {
        Ok(name)
    } else {
        // No match found! If the assumptions of this file were met for the binary under analysis,
        // this means that we attempted to call a trait method on a trait object despite no
        // implementations of that trait existing. Most likely, this means that we are executing an
        // impossible path (e.g. a path where a client option will in reality always be None, but
        // haybale does not know that because it does not have visibility into how capsules and
        // peripherals are setup at boot. Return an error indicating that no match was found
        Err(DynDispatchLookupError::NoImplementationsFound)
    }
}

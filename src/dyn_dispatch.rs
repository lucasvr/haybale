/// Much of this file is copied from the main thing I wrote to prevent circular deps.
/// TODO: Reorganize this so there isn't code duplication.
/// TODO: Make use of this dependent on config
/// TODO: Move MIR files into memory once at start so rebuilding during execution is okay
/// TODO: One potential issue with the logic here is that finding the longest path for any input
/// is not the same as the longest path with the current constraints. So here we are finding the
/// longest possible path for any input, then assuming that is also the longest path with current
/// constraints, which might lead to finding a path that is not the longest path. Potential fixes
/// include a) what I have always wanted, which is treating trait object calls as branches and
/// evaluating all paths with current constraints or b) something similar but short of that where
/// all paths are evaluated with current constraints in a new haybale run, then we pass the
/// concrete function once we have found the longest.
use crate::backend::*;
use crate::*;
use std::collections::HashSet;
use std::result::Result;
use std::string::String;

/// Returns the number of LLVM instructions in this path.
/// A path is represented as a vector of `PathEntry`s, and
/// each PathEntry describes a sequential set of instructions in a basic block,
/// not necessarily starting at the beginning of that basic block.
/// Thus we have to investigate each path entry to count the number of instructions
/// described by it.
/// However, function calls complicate this: if function calls are not inlined, then the entire
/// function is counted as a single instruction!
fn get_path_length<'p>(path: &Vec<PathEntry<'p>>) -> usize {
    path.iter().fold(0, |acc, entry| {
        let location = &entry.0;
        // TODO: Below assumes terminator is not an instruction, not totally clear on how this
        // works though.
        let entry_len = match location.instr {
            BBInstrIndex::Instr(idx) => location.bb.instrs.len() - idx,
            BBInstrIndex::Terminator => 0,
        };
        acc + entry_len
    })
}

/// Given a function name and project/configuration, returns the longest path
/// (in llvm IR "instructions") through that function, as well as a copy of the `State` of
/// the execution manager at the conclusion of symbolically executing that path. Ties
/// are broken at random.
fn find_longest_path<'p, B: Backend>(
    funcname: &str,
    project: &'p Project,
    config: Config<'p, B>,
) -> Option<(usize, State<'p, B>)> {
    let mut em: ExecutionManager<B> = symex_function(funcname, project, config, None).unwrap();
    //TODO: Following code could probably be more functional
    let mut longest_path_len = 0;
    let mut longest_path_state = None;
    loop {
        match em.next() {
            Some(res) => match res {
                Ok(_) => {
                    println!("dyn_dispatch: {:?}, next() worked", funcname);
                }
                Err(e) => {
                    panic!(em.state().full_error_message_with_context(e));
                }
            },
            None => break,
        }
        let state = em.state();
        let path = state.get_path();
        let len = get_path_length(path);
        if len > longest_path_len {
            longest_path_len = len;
            longest_path_state = Some(state.clone());
        }
    }
    longest_path_state.map_or(None, |state| Some((longest_path_len, state)))
}

/// Return the longest possible path for a given method call on a trait object.
pub(crate) fn longest_path_dyn_dispatch<'p, B: Backend>(
    project: &'p Project,
    config: Config<'p, B>,
    method_name: &str,
    trait_name: &str,
) -> Result<&'p str, String> {
    // First, check if we have already done a lookup for this trait method. For now use a global
    // for ease, though a field on the project would work better (but would require adding lots
    // of lifetime annotations).
    let map = project.trait_obj_map.try_lock().unwrap();
    let lookup = map.get(&(method_name.to_string(), trait_name.to_string()));
    match lookup {
        Some(s) => {
            println!("Longest lookup match!");
            return Ok(project.get_func_by_name(s).unwrap().0.name.as_str());
        }
        _ => {}
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
        println!("num_matches: {:?}", num_matches);
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
                println!("STORING IN detected_recursion");
                continue;
            }
            println!("tracing {:?}", f.name);
            under_analysis_set.insert(f.name.to_string()); //store mangled name of the function we are tracing.
            drop(under_analysis_set); // unlock mutex
            if let Some((len, _state)) = find_longest_path(&f.name, &project, config.clone()) {
                if len > longest {
                    longest = len;
                    longest_func_name = Some(&f.name);
                }
            }

            let mut under_analysis_set = project.trait_under_analysis.try_lock().unwrap();
            assert!(under_analysis_set.remove(&f.name.to_string())); //assert so we panic if it wasnt there, which would be an error
        }
        println!("longest match: {:?}", longest_func_name.unwrap());
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
        let mut map = project.trait_obj_map.try_lock().unwrap();
        map.insert(
            (method_name.to_string(), trait_name.to_string()),
            longest_func_name.unwrap().to_string(),
        );
    } else {
        println!("Skipping save optimization, executing concrete function with recursion");
    }

    Ok(longest_func_name.unwrap())
}

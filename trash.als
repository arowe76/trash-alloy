// ==============================================================================
// Signatures
// ==============================================================================

/**
* File is a variable set of currently existing files. The universe may contain up to the scope
* number of File atoms.
*/
var sig File {}

/**
* Trash is a variable subset of File.  Structural invariant: Trash ⊆ File in every state.
*/
var sig Trash in File {}


// ==============================================================================
// Operations (Transitions)
// ==============================================================================

/**
* @ empty()
*   Removes all files currently in Trash from the system permanently.
*/
pred empty {
  some Trash             // guard: only allowed if trash is nonempty...
  no Trash'              // add file to trash...
  File' = File - Trash.  // file still exists.
}

/**
* @ delete(f)
*   Moves a file into Trash without removing it from File.
*   This models a soft delete.
*/
pred delete [f : File] {
  not (f in Trash)       // guard: cannot delete something already in trash...
  Trash' = Trash + f     // add file to trash...
  File' = File           // file still exists.
}

/**
* @ restore(f)
*   Removes a file from Trash and restores it to active files.
*/
pred restore [f : File] {
  f in Trash            // guard: must be in trash...
  Trash' = Trash - f    // remove from trash...
  File' = File          // file remains in File.
}

/**
* @ stutter()
*   Allows the system to remain in a terminal configuration while still satisfying 
*   "always (some transition occurs)". This is necessary to allow the system to reach a
*   state, where no File exists.
*/
pred stutter {
  File' = File
  Trash' = Trash 
}

/**
* @ purge(f)
*   Permanently deletes a file that is already in Trash.
*   This models a hard deleting from the trash.
*/
pred purge [f : File] {
  f in Trash           // guard: f must be in the Trash...
  Trash' = Trash - f   // effect: f is removed from Trash...
  File' = File - f     // effect: f is removed from File.
}


// ==============================================================================
// Transition System Constraint
// ==============================================================================

/**
* @ trans()
*   At every state in the trace, at least one transistion must be enabled.
*   This enforces progress in the transistion system.
*   
*   Because stutter() is included, terminal configurations.
*   (e.g., not File and no Trash) are now allowed.
*/
fact trans {
  always (stutter or empty or (some f : File | delete[f] or restore[f] or purge[f]))
}


// ==============================================================================
// Run Commands
// ==============================================================================

/**
*   --Run #1--
*   Start with some File and empty Trash...
*   Show that trash can become nonempty and later empty again...
*   Demonstrates that deletion + handling of trash is possible... 
*/
run { some File and no Trash
           eventually (some Trash) 
           eventually (no Trash)
} for 3 but 6 steps

/**
*   --Run #2--
*   Start with some File and empty Trash...
*   Eventually reach a state where Trash is empty and the number of Files has
*   strictly decreased.
*   Demonstrates that permanent deletion (via purge() or empty()) actually
*   reduces the system.
*/
run { some File and no Trash
           eventually (some Trash)
           eventually (no Trash and some File and #File < 3)
} for 3 but 8 steps


// ==============================================================================
// Temporal Properties
// ==============================================================================

/**
*   --Assertion #1 (Safety Property)--
*   Trash is always a subset of File.
*   This should hold because Trash is declared "in File" and transistions
*   preserve the invariant.
*/
assert TrashAlwaysSubsetOfFile {
  always (Trash in File)
}
check TrashAlwaysSubsetOfFile for 2 but 4 steps

/**
*   --Assertion #2 (Liveness Property)--
*   If a file is in Trash, it will eventually not be in Trash.
*   
*   Note: This may fail because stutter() allows the system to remain in a 
*   state forever without making progress.  Alloy may produce a counterexample
*   where a file stays in Trash indefinitely. 
*/
assert TrashEventuallyLeavesTrash {
  always (all f: File | (f in Trash) implies eventually (f not in Trash))
}
check TrashEventuallyLeavesTrash for 2 but 6 steps
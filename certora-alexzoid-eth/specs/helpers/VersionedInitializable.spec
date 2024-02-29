///////////////// METHODS //////////////////////

///////////////// DEFINITIONS /////////////////////

////////////////// FUNCTIONS //////////////////////

///////////////// GHOSTS & HOOKS //////////////////

//
// VersionedInitializable initial values
//

ghost bool ghostInitializing {
    init_state axiom ghostInitializing == false;
}

hook Sload bool val currentContract.initializing STORAGE {
    require(val == ghostInitializing);
}

hook Sstore currentContract.initializing bool val STORAGE {
    ghostInitializing = val;
}

ghost uint256 ghostLastInitializedRevision {
    init_state axiom ghostLastInitializedRevision == 0;
}

hook Sload uint256 val currentContract.lastInitializedRevision STORAGE {
    require(val == ghostLastInitializedRevision);
}

hook Sstore currentContract.lastInitializedRevision uint256 val STORAGE {
    ghostLastInitializedRevision = val;
}

///////////////// PROPERTIES //////////////////////

// Initialize could be executed once
rule initializeCouldBeExecutedOnce(env e1, calldataarg args1, env e2, calldataarg args2) {

    require(ghostLastInitializedRevision == 0);
    require(ghostInitializing == false);

    initialize@withrevert(e1, args1);
    bool firstCallReverted = lastReverted;

    initialize@withrevert(e2, args2);
    bool secondCallReverted = lastReverted;

    assert(!firstCallReverted => secondCallReverted);
}


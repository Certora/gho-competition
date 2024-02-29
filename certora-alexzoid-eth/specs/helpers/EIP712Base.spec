///////////////// METHODS //////////////////////

///////////////// DEFINITIONS /////////////////////

////////////////// FUNCTIONS //////////////////////

///////////////// GHOSTS & HOOKS //////////////////

//
// Ghost copy of `_domainSeparator`
//
// Uncommenting this block leads to unexpected errors in Prover
// uncommented: https://prover.certora.com/output/52567/3fce257bd5bd447db7f25eb12b961f05/?anonymousKey=001f36a371acf2f144e09f729eee9da2ac9878e4
// commented: https://prover.certora.com/output/52567/1e25deaa8cd148bc88fcb323adeef0db/?anonymousKey=38ada586409811a6877cbfc14a8d5f7f3251bbaf
// discord issue: https://discord.com/channels/795999272293236746/1160743011735580712
ghost bytes32 ghostDomainSeparator {
    init_state axiom ghostDomainSeparator == to_bytes32(0);
}

hook Sload bytes32 val currentContract._domainSeparator STORAGE {
    require(ghostDomainSeparator == val);
}
/*
hook Sstore currentContract._domainSeparator bytes32 val STORAGE {
    ghostDomainSeparator = val;
}
*/

///////////////// PROPERTIES //////////////////////

// Domain separator depends on token name
rule domainSeparatorDepensOnName(env e) {
    
    setName1();
    bytes32 separator1 = calculateDomainSeparator(e);

    setName2();
    bytes32 separator2 = calculateDomainSeparator(e);

    assert(separator1 != separator2);
}


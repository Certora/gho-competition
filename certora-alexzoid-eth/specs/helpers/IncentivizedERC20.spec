///////////////// METHODS //////////////////////

///////////////// DEFINITIONS /////////////////////

////////////////// FUNCTIONS //////////////////////

///////////////// GHOSTS & HOOKS //////////////////

//
// Ghost copy of `decimals`
//

ghost uint8 ghostDecimals {
    init_state axiom ghostDecimals == 0;
}

hook Sload uint8 val currentContract._decimals STORAGE {
    require(ghostDecimals == val);
}

hook Sstore currentContract._decimals uint8 val STORAGE {
    ghostDecimals = val;
}

//
// Ghost copy of `_incentivesController`
//

ghost address ghostIncentivesController {
    init_state axiom ghostIncentivesController == 0;
}

hook Sload address val currentContract._incentivesController STORAGE {
    require(ghostIncentivesController == val);
}

hook Sstore currentContract._incentivesController address val STORAGE {
    ghostIncentivesController = val;
}

///////////////// PROPERTIES //////////////////////


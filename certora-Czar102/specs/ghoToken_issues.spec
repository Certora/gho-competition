import "ghoToken.spec";

use invariant inv_balanceOf_leq_totalSupply;
use invariant level_leq_sumAllLevel;
use invariant facilitatorsList_setInvariant;
use invariant addr_in_set_iff_in_map;
use invariant valid_facilitatorLabel;
use invariant sumAllBalance_eq_totalSupply;

/**
* @title makes sure that the facilitator behavior is as it should be
* GitHub issue: https://github.com/Czar102/gho-verification/issues/3
* run failure example: https://prover.certora.com/output/2949/4ed4524e8cd94101b40b3edb5d646905/?anonymousKey=7d52871cc797120d42a80486763e762aefccbf0f
*/
rule facilitatorRemovalRevertReason() {
	env e;
	address facilitator;
	bool was_facilitator = inFacilitatorsMapping[facilitator];
	uint128 limit;

	removeFacilitator@withrevert(e, facilitator);
	bool reverted = lastReverted;

	assert reverted <=> (
		!was_facilitator ||
		!hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender) ||
		/* this is a bug, shouldn't be here but I'm adding it so that the spec
		will pass on the original contract */
		// bucket_level[facilitator] != 0 ||
		e.msg.value != 0
	), "Should have (not) reverted";

	assert !reverted => (
		!inFacilitatorsMapping[facilitator] &&
		bucket_level[facilitator] == 0 &&
		bucket_capacity[facilitator] == 0
	), "State change is incorrect";
}

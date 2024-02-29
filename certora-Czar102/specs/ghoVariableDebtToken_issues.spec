import "ghoVariableDebtToken.spec";

use invariant discountCantExceed100Percent;

function areRoughlyTheSame(mathint a, mathint b) returns bool {
	// values are roughly the same if they differ by less than one millionth of the larger
	// plus 10 wei (as an excessive rounding error)

	mathint max = b;
	if (a > b) {
		max = a;
	}

	mathint max_err = max / 1000000 + 10;

	return (a + max_err >= b) && (b + max_err >= a);
}

/**
* @title Debt accrual can't cause any major discrepancies in the future balance of the debt token
* Description available in issue: https://github.com/Czar102/gho-verification/issues/1
* Run example available on the prover website: https://prover.certora.com/output/2949/68662d620d5a44b2bfe8c163b69a1775?anonymousKey=9393726ebbbdcbad59c4d9f2859b84f56070707d
**/
rule lackOfUpdatesDoesntCauseHarm() {
	address user;
	env e_init; env e_mid; env e_end;
	require e_init.block.timestamp < e_mid.block.timestamp;
	require e_mid.block.timestamp < e_end.block.timestamp;

	// make more constraints to prevernt timeouts
	require balanceOfDiscountTokenAtTimestamp(user, e_init.block.timestamp) ==
		balanceOfDiscountTokenAtTimestamp(user, e_mid.block.timestamp) &&
		balanceOfDiscountTokenAtTimestamp(user, e_mid.block.timestamp) ==
		balanceOfDiscountTokenAtTimestamp(user, e_end.block.timestamp);

	// let's further constrain the indexes at those times so that the prover will have
	// less nonlinear equations to consider

	// Let's double the inde every time we do stuff
	require indexAtTimestamp(e_init.block.timestamp) == ray() &&
		to_mathint(indexAtTimestamp(e_mid.block.timestamp)) == 2 * ray() &&
		to_mathint(indexAtTimestamp(e_end.block.timestamp)) == 4 * ray();

	requireInvariant discountCantExceed100Percent(user);

	uint initBalance = balanceOf(e_init, user);

	// it's not needed, but for the sake of nice numbers
	require getUserCurrentIndex(e_init, user) == ray();
	require getUserDiscountRate(e_init, user) == 3000; // 30%, the maximum
	require balanceOf(e_init, user) == 1000;

	uint finalBalanceNoAction = balanceOf(e_end, user);

	accrueDebt(e_mid, user);

	uint finalBalanceWithUpdate = balanceOf(e_end, user);

	assert areRoughlyTheSame(finalBalanceNoAction, finalBalanceWithUpdate);
}
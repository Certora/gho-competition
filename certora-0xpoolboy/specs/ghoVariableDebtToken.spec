import "VariableDebtToken.spec";

using GhoDiscountRateStrategy as discStrategy;
using DummyERC20WithTimedBalanceOf as discountToken;
using DummyPool as pool;

methods{
	
  	/***********************************;
    *    PoolAddressesProvider.sol     *;
    ************************************/
	function _.getACLManager() external => CONSTANT;

	/************************;
    *    ACLManager.sol     *;
    *************************/

	function _.isPoolAdmin(address user) external => retreivePoolAdminFromGhost(user) expect bool ALL;

	/******************************************************************;
	*	DummyERC20WithTimedBalanceOf.sol (linked to _discountToken)   *;
	*******************************************************************/
	// represent a random balance per block 
	function discountToken.balanceOf(address user) external returns (uint256) with (env e) => balanceOfDiscountTokenAtTimestamp(user, e.block.timestamp) ;

  	/************************************;
    *   DummyPool.sol (linked to POOL)  *;
    *************************************/
	// represent a random index per block
	function pool.getReserveNormalizedVariableDebt(address asset) external returns (uint256) with (env e) => indexAtTimestamp(e.block.timestamp);

	/************************************;
	*	GhoVariableDebtTokenHarness.sol	*;
	*************************************/
	function discStrategy.calculateDiscountRate(uint256, uint256) external returns (uint256) envfree;

	/************************************;
	*	GhoVariableDebtTokenHarness.sol	*;
	*************************************/
	function getUserCurrentIndex(address) external returns (uint256) envfree;
	function getUserDiscountRate(address) external returns (uint256) envfree;
	function getUserAccumulatedDebtInterest(address) external returns (uint256) envfree;
	function getBalanceOfDiscountToken(address) external returns (uint256);
	function getBalanceIncreaseAndDiscountScaled(address, uint256, uint256, uint256) external returns (uint256, uint256) envfree;

	/********************************;
	*	GhoVariableDebtToken.sol	*;
	*********************************/
	function totalSupply() external returns(uint256) envfree;
	function balanceOf(address) external returns (uint256);
	function mint(address, address, uint256, uint256) external returns (bool, uint256);
	function burn(address ,uint256 ,uint256) external returns (uint256);
	function scaledBalanceOf(address) external returns (uint256) envfree;
	function getBalanceFromInterest(address) external returns (uint256) envfree;
	function rebalanceUserDiscountPercent(address) external;
	function updateDiscountDistribution(address ,address ,uint256 ,uint256 ,uint256) external;
	function getIncentivesController() external returns (address) envfree;
	function getDiscountRateStrategy() external returns (address) envfree;
	function getDiscountToken() external returns (address) envfree;
	function getAToken() external returns (address) envfree;
	function borrowAllowance(address, address) external returns (uint256) envfree;
	function POOL() external returns (address) envfree;
	function getDiscountPercent(address user) external returns (uint256) envfree;

	function decimals() external returns (uint8) envfree;
	function UNDERLYING_ASSET_ADDRESS() external returns (address) envfree;
	function DEBT_TOKEN_REVISION() external returns (uint256) envfree;


	function VersionedInitializable.isConstructor() internal returns (bool) => isConstructorFromGhost();
}

/**
* CVL implementation of rayMul
**/
function rayMulCVL(uint256 a, uint256 b) returns mathint {
	return ((a * b + (ray() / 2)) / ray());
}
function rayDivCVL(uint256 a, uint256 b) returns mathint {
	return ((a * ray() + (b / 2)) / b);
}
// function percentMulCVL(uint256 v, uint256 p) returns mathint {
// 	return ((v * p + 5000) / 10000);
// }

//todo: check balanceof after mint (stable index), burn after balanceof

definition MAX_DISCOUNT() returns uint256 = 10000; // equals to 100% discount, in points

ghost mapping(address => mapping (uint256 => uint256)) discount_ghost;
ghost mapping(uint256 => uint256) index_ghost;
// keeps track of users with pool admin permissions in order to return a consistent value per user
ghost mapping(address => bool) poolAdmin_ghost;

// returns whether the user is a pool admin
function retreivePoolAdminFromGhost(address user) returns bool{
    return poolAdmin_ghost[user];
}

/**
* Query index_ghost for the index value at the input timestamp
**/
function indexAtTimestamp(uint256 timestamp) returns uint256 {
    require index_ghost[timestamp] >= ray();
    return index_ghost[timestamp];
    // return 1001684385021630839436707910;//index_ghost[timestamp];
}

/**
* Query discount_ghost for the [user]'s balance of discount token at [timestamp]
**/
function balanceOfDiscountTokenAtTimestamp(address user, uint256 timestamp) returns uint256 {
	return discount_ghost[user][timestamp];
}

/**
* Returns an env instance with [ts] as the block timestamp
**/
function envAtTimestamp(uint256 ts) returns env {
	env e;
	require(e.block.timestamp == ts);
	return e;
}

// Reverting functions

definition functionsThatRevert(method f) returns bool =
	f.selector == sig:transfer(address, uint256).selector
	|| f.selector == sig:transferFrom( address, address, uint256).selector
	|| f.selector == sig:allowance(address, address).selector
	|| f.selector == sig:approve(address, uint256).selector
	|| f.selector == sig:increaseAllowance(address, uint256).selector
	|| f.selector == sig:decreaseAllowance(address, uint256).selector;


rule functionsShouldRevert(
	env e,
	method f,
	calldataarg args
) filtered { f -> functionsThatRevert(f) } {
	f@withrevert(e, args);
	assert lastReverted;
}

rule sanity(
	env e,
	method f,
	calldataarg args
) filtered { f -> !functionsThatRevert(f) } {
	f(e, args);
	satisfy true;
}

/**
* @title at any point in time, the user's discount rate isn't larger than 100%
**/
invariant discountCantExceed100Percent(address user)
	getUserDiscountRate(user) <= MAX_DISCOUNT()
	filtered {
		f -> !functionsThatRevert(f)
	}
	{
		preserved updateDiscountDistribution(address sender,address recipient,uint256 senderDiscountTokenBalance,uint256 recipientDiscountTokenBalance,uint256 amount) with (env e) {
			require(indexAtTimestamp(e.block.timestamp) >= ray());
		}
	}

/**
* Imported rules from VariableDebtToken.spec
**/
//pass
use rule disallowedFunctionalities;


/**
* @title proves that the user's balance of debt token (as reported by GhoVariableDebtToken::balanceOf) can't increase by calling any external non-mint function.
**/
//pass
rule nonMintFunctionCantIncreaseBalance(
	method f
) filtered {
	f-> f.selector != sig:mint(address, address, uint256, uint256).selector
	 && !functionsThatRevert(f)
} {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	// Forcing the index to be fixed (otherwise the rule times out). For non-fixed index replace `==` with `>=`
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) == indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);

	env e = envAtTimestamp(ts2);
	uint256 balanceBeforeOp = balanceOf(e, user);
	calldataarg args;
	f(e,args);
	mathint balanceAfterOp = balanceOf(e, user);
	mathint allowedDiff = indexAtTimestamp(ts2) / ray();
	// assert(balanceAfterOp != balanceBeforeOp + allowedDiff + 1);
	assert(balanceAfterOp <= balanceBeforeOp + allowedDiff);
}

/**
* @title proves that a call to a non-mint operation won't increase the user's balance of the actual debt tokens (i.e. it's scaled balance)
**/
// pass
rule nonMintFunctionCantIncreaseScaledBalance(
	method f
) filtered {
	f-> f.selector != sig:mint(address, address, uint256, uint256).selector
	 && !functionsThatRevert(f)
} {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = scaledBalanceOf(user);
	env e = envAtTimestamp(ts2);
	calldataarg args;
	f(e,args);
	uint256 balanceAfterOp = scaledBalanceOf(user);
	assert(balanceAfterOp <= balanceBeforeOp);
}

/**
* @title proves that debt tokens aren't transferable
**/
// pass
rule debtTokenIsNotTransferable(method f) filtered { f -> !functionsThatRevert(f) } {
	address user1;
	address user2;
	require(user1 != user2);
	uint256 scaledBalanceBefore1 = scaledBalanceOf(user1);
	uint256 scaledBalanceBefore2 = scaledBalanceOf(user2);
	env e;
	calldataarg args;
	f(e,args);
	uint256 scaledBalanceAfter1 = scaledBalanceOf(user1);
	uint256 scaledBalanceAfter2 = scaledBalanceOf(user2);

	assert( scaledBalanceBefore1 + scaledBalanceBefore2 == scaledBalanceAfter1 + scaledBalanceAfter2 
	=> (scaledBalanceBefore1 == scaledBalanceAfter1 && scaledBalanceBefore2 == scaledBalanceAfter2));
}

/**
* @title proves that only burn/mint/rebalanceUserDiscountPercent/updateDiscountDistribution can modify user's scaled balance
**/
// pass
rule onlyCertainFunctionsCanModifyScaledBalance(method f) filtered { f -> !functionsThatRevert(f) } {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = scaledBalanceOf(user);
	env e = envAtTimestamp(ts2);
	calldataarg args;
	f(e,args);
	uint256 balanceAfterOp = scaledBalanceOf(user);
	assert(balanceAfterOp != balanceBeforeOp => (
		(f.selector == sig:mint(address ,address ,uint256 ,uint256).selector) ||
		(f.selector == sig:burn(address ,uint256 ,uint256).selector) ||
		(f.selector == sig:updateDiscountDistribution(address ,address ,uint256 ,uint256 ,uint256).selector) ||
		(f.selector == sig:rebalanceUserDiscountPercent(address).selector)));
}

/**
* @title proves that only a call to decreaseBalanceFromInterest will decrease the user's accumulated interest listing.
**/
// pass
rule userAccumulatedDebtInterestWontDecrease(method f) filtered { f -> !functionsThatRevert(f) } {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 initAccumulatedInterest = getUserAccumulatedDebtInterest(user);
	env e2 = envAtTimestamp(ts2);
	calldataarg args;
	f(e2,args);
	uint256 finAccumulatedInterest = getUserAccumulatedDebtInterest(user);
	assert(initAccumulatedInterest > finAccumulatedInterest => f.selector == sig:decreaseBalanceFromInterest(address, uint256).selector);
}

/**
* @title proves that a user can't nullify its debt without calling burn
**/
// pass
rule userCantNullifyItsDebt(method f) filtered { f -> !functionsThatRevert(f) } {
    address user;
    env e;
    env e2;
	require(getUserCurrentIndex(user) == indexAtTimestamp(e.block.timestamp));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = balanceOf(e, user);
	calldataarg args;
    require e2.block.timestamp == e.block.timestamp;
	f(e2,args);
	uint256 balanceAfterOp = balanceOf(e, user);
	assert((balanceBeforeOp > 0 && balanceAfterOp == 0) => (f.selector == sig:burn(address, uint256, uint256).selector));
}

/***************************************************************
* Integrity of Mint
***************************************************************/

/**
* @title proves that after calling mint, the user's discount rate is up to date
**/
rule integrityOfMint_updateDiscountRate() {
	address user1;
	address user2;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	mint(e, user1, user2, amount, index);
	uint256 debtBalance = balanceOf(e, user2);
	uint256 discountBalance = getBalanceOfDiscountToken(e, user2);
	uint256 discountRate = getUserDiscountRate(user2);
	assert(discStrategy.calculateDiscountRate(debtBalance, discountBalance) == discountRate);
}

/**
* @title proves the after calling mint, the user's state is updated with the recent index value
**/
rule integrityOfMint_updateIndex() {
	address user1;
	address user2;
	env e;
	uint256 amount;
	uint256 index;
	mint(e, user1, user2, amount, index);
	assert(getUserCurrentIndex(user2) == index);
}

/**
* @title proves that on a fixed index calling mint(user, amount) will increase the user's scaled balance by amount. 
**/
// pass
rule integrityOfMint_updateScaledBalance_fixedIndex() {
	address user;
	env e;
	uint256 balanceBefore = balanceOf(e, user);
	uint256 scaledBalanceBefore = scaledBalanceOf(user);
	address caller;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	require(getUserCurrentIndex(user) == index);
	mint(e, caller, user, amount, index);

	uint256 balanceAfter = balanceOf(e, user);
	mathint scaledBalanceAfter = scaledBalanceOf(user);
	mathint scaledAmount = rayDivCVL(amount, index);

	assert(scaledBalanceAfter == scaledBalanceBefore + scaledAmount);
}

/**
* @title proves that mint can't effect other user's scaled balance
**/
// pass
rule integrityOfMint_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 index;
	address targetUser;
	address caller;
	mint(e, caller, targetUser, amount, index);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}

/**
* @title proves that when calling mint, the user's balance (as reported by GhoVariableDebtToken::balanceOf) will increase if the call is made on bahalf of the user.
**/
rule onlyMintForUserCanIncreaseUsersBalance() {
	address user1;
    env e;
	require(getUserCurrentIndex(user1) == indexAtTimestamp(e.block.timestamp));
	
	uint256 finBalanceBeforeMint = balanceOf(e, user1);
	uint256 amount;
	mint(e,user1, user1, amount, indexAtTimestamp(e.block.timestamp));
	uint256 finBalanceAfterMint = balanceOf(e, user1);

	assert(finBalanceAfterMint != finBalanceBeforeMint);
}

/**
* @title proves that mint can't effect other user's scaled balance
**/
// pass
rule integrityOfMint_decreaseBorrowAllowance(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require user != onBehalfOf; // FIXME
	mathint allowanceBefore = borrowAllowance(onBehalfOf, user);
	mint(e, user, onBehalfOf, amount, index);
	mathint allowanceAfter = borrowAllowance(onBehalfOf, user);

	assert allowanceBefore >= to_mathint(amount);
	assert allowanceAfter + amount == allowanceBefore;
	//uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
}

//pass
use rule integrityMint_atoken;

rule integrityOfMint_revertsWhenScaledAmountZero(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;
	mathint amountScaled = rayDivCVL(amount, index);

	mint@withrevert(e, user, onBehalfOf, amount, index);

	assert amountScaled == 0 => lastReverted;
}

// TODO2 split the rule, require more and try to make it pass
rule integrityOfMint_mintCorrectAmount(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;

	mathint amountScaled = rayDivCVL(amount, index);
	require amountScaled != 0;

	uint256 scaledBalanceBefore = scaledBalanceOf(onBehalfOf);
	uint256 discountPercent = getDiscountPercent(onBehalfOf);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(onBehalfOf, scaledBalanceBefore, discountPercent, index);

	mint(e, user, onBehalfOf, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(e, onBehalfOf);

	assert (
		amountScaled > discountScaled
	) => (
		scaledBalanceAfter - scaledBalanceBefore == amountScaled - discountScaled
	);

	assert (
		amountScaled <= discountScaled
	) => (
		scaledBalanceBefore - scaledBalanceAfter == discountScaled - amountScaled
	);
}

// PASS
rule integrityOfMint_mintCorrectAmount1(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;

	mathint amountScaled = rayDivCVL(amount, index);
	require amountScaled != 0;

	uint256 scaledBalanceBefore = scaledBalanceOf(onBehalfOf);
	uint256 discountPercent = getDiscountPercent(onBehalfOf);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(onBehalfOf, scaledBalanceBefore, discountPercent, index);
	require amountScaled > discountScaled; // CASE 1

	mint(e, user, onBehalfOf, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(e, onBehalfOf);

	assert (
		scaledBalanceAfter - scaledBalanceBefore == amountScaled - discountScaled
	);
}

// PASS
rule integrityOfMint_mintCorrectAmount2(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;

	mathint amountScaled = rayDivCVL(amount, index);
	require amountScaled != 0;

	uint256 scaledBalanceBefore = scaledBalanceOf(onBehalfOf);
	uint256 discountPercent = getDiscountPercent(onBehalfOf);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(onBehalfOf, scaledBalanceBefore, discountPercent, index);
	require amountScaled <= discountScaled; // CASE 2

	mint(e, user, onBehalfOf, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(e, onBehalfOf);

	assert (
		scaledBalanceBefore - scaledBalanceAfter == discountScaled - amountScaled
	);
}

// PASS
rule integrityOfMint_conditionalSatisfiability1(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;

	mathint amountScaled = rayDivCVL(amount, index);

	uint256 scaledBalanceBefore = scaledBalanceOf(onBehalfOf);
	uint256 discountPercent = getDiscountPercent(onBehalfOf);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(onBehalfOf, scaledBalanceBefore, discountPercent, index);

	mint(e, user, onBehalfOf, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(e, onBehalfOf);

	satisfy (amountScaled > discountScaled);
}

// PASS
rule integrityOfMint_conditionalSatisfiability2(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount,
	uint256 index
) {
	require index != 0;

	mathint amountScaled = rayDivCVL(amount, index);

	uint256 scaledBalanceBefore = scaledBalanceOf(onBehalfOf);
	uint256 discountPercent = getDiscountPercent(onBehalfOf);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(onBehalfOf, scaledBalanceBefore, discountPercent, index);

	mint(e, user, onBehalfOf, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(e, onBehalfOf);

	satisfy (amountScaled < discountScaled);
}

/***************************************************************
* Integrity of Burn
***************************************************************/

/**
* @title proves that after calling burn, the user's discount rate is up to date
**/
rule integrityOfBurn_updateDiscountRate() {
	address user;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	burn(e, user, amount, index);
	uint256 debtBalance = balanceOf(e, user);
	uint256 discountBalance = getBalanceOfDiscountToken(e, user);
	uint256 discountRate = getUserDiscountRate(user);
	assert(discStrategy.calculateDiscountRate(debtBalance, discountBalance) == discountRate);
}

/**
* @title proves the after calling burn, the user's state is updated with the recent index value
**/
rule integrityOfBurn_updateIndex() {
	address user;
	env e;
	uint256 amount;
	uint256 index;
	burn(e, user, amount, index);
	assert(getUserCurrentIndex(user) == index);
}

/**
* @title proves that calling burn with 0 amount doesn't change the user's balance
**/
use rule burnZeroDoesntChangeBalance;

/**
* @title proves a concrete case of repaying the full debt that ends with a zero balance
**/
rule integrityOfBurn_fullRepay_concrete() {
	env e;
	address user;
	uint256 currentDebt = balanceOf(e, user);
	uint256 index = indexAtTimestamp(e.block.timestamp);
	// handle timeouts
	require(getUserCurrentIndex(user) == ray());
	require(to_mathint(index) == 2*ray());
	require(to_mathint(scaledBalanceOf(user)) == 4*ray());
	
	burn(e, user, currentDebt, index);
	uint256 scaled = scaledBalanceOf(user);
	assert(scaled == 0);
}


/**
* @title proves that burn can't effect other user's scaled balance
**/
// pass
rule integrityOfBurn_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 index;
	address targetUser;
	burn(e,targetUser, amount, index);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}

// pass
/**
* @title proves that burn reverts when scaled amount is zero.
**/
rule integrityOfBurn_revertsWhenScaledAmountZero(
	env e,
	address from,
	uint256 amount,
	uint256 index
) {
	require index != 0;
	mathint amountScaled = rayDivCVL(amount, index);

	burn@withrevert(e, from, amount, index);

	assert amountScaled == 0 => lastReverted;
}

// pass
/**
* @title proves that the remaining scaled balance is burned.
**/
rule integrityOfBurn_burnCorrectAmount1(
	env e,
	address from,
	uint256 amount,
	uint256 index
) {
	require index != 0;
	mathint amountScaled = rayDivCVL(amount, index);
	require amountScaled != 0;

	uint256 balanceBeforeBurn = balanceOf(e, from);
	uint256 scaledBalanceBefore = scaledBalanceOf(from);

	require amount == balanceBeforeBurn; // CASE 1

	uint256 discountPercent = getDiscountPercent(from);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(from, scaledBalanceBefore, discountPercent, index);

	burn(e, from, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(from);

	assert scaledBalanceAfter == 0;
}

// timesout but catches bugs
/**
* @title proves that the scaled balance is reduced by the correct amount, considering the discount.
**/
rule integrityOfBurn_burnCorrectAmount2(
	env e,
	address from,
	uint256 amount,
	uint256 index
) {
	require index != 0;
	mathint amountScaled = rayDivCVL(amount, index);
	require amountScaled != 0;

	uint256 balanceBeforeBurn = balanceOf(e, from);
	uint256 scaledBalanceBefore = scaledBalanceOf(from);

	require amount != balanceBeforeBurn; // CASE 2

	uint256 discountPercent = getDiscountPercent(from);
	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(from, scaledBalanceBefore, discountPercent, index);

	burn(e, from, amount, index);

	uint256 scaledBalanceAfter = scaledBalanceOf(from);

	assert scaledBalanceAfter + require_uint128(amountScaled + discountScaled) == to_mathint(scaledBalanceBefore);
}



/**
* @title proves the after calling updateDiscountDistribution, the user's state is updated with the recent index value
**/
rule integrityOfUpdateDiscountDistribution_updateIndex() {
	address sender;
	address recipient;
	uint256 senderDiscountTokenBalance;
    uint256 recipientDiscountTokenBalance;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);
	assert(scaledBalanceOf(sender) > 0 => getUserCurrentIndex(sender) == index);
	assert(scaledBalanceOf(recipient) > 0 => getUserCurrentIndex(recipient) == index);
}


/**
* @title proves that updateDiscountDistribution can't effect other user's scaled balance
**/
// pass
rule integrityOfUpdateDiscountDistribution_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 senderDiscountTokenBalance;
	uint256 recipientDiscountTokenBalance;
	address sender;
	address recipient;
	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => (otherUser == sender || otherUser == recipient));
}

//pass
/**
* @title proves that updateDiscountDistribution updates discountPercent for sender.
**/
rule integrityOfUpdateDiscountDistribution_updateDiscountRate_sender(
	env e,
	address sender,
    address recipient,
    uint256 senderDiscountTokenBalance,
    uint256 recipientDiscountTokenBalance,
    uint256 amount
) {
	uint256 index = indexAtTimestamp(e.block.timestamp);

	require scaledBalanceOf(sender) != 0;
	require scaledBalanceOf(recipient) == 0;

	mathint discountPercentSenderBefore = getDiscountPercent(sender);

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	mathint estimatedDiscountPercentSender = require_uint16(discStrategy.calculateDiscountRate(
												require_uint256(rayMulCVL(scaledBalanceOf(sender), index)),
												require_uint256(senderDiscountTokenBalance - amount)
											));

	mathint discountPercentSenderAfter = getDiscountPercent(sender);

	assert discountPercentSenderAfter == estimatedDiscountPercentSender;
}

//pass
/**
* @title proves that updateDiscountDistribution updates discountPercent for recipient.
**/
rule integrityOfUpdateDiscountDistribution_updateDiscountRate_recipient(
	env e,
	address sender,
    address recipient,
    uint256 senderDiscountTokenBalance,
    uint256 recipientDiscountTokenBalance,
    uint256 amount
) {
	uint256 index = indexAtTimestamp(e.block.timestamp);

	require scaledBalanceOf(sender) == 0;
	require scaledBalanceOf(recipient) != 0;

	mathint discountPercentRecipientBefore = getDiscountPercent(recipient);

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	mathint estimatedDiscountPercentSender = require_uint16(discStrategy.calculateDiscountRate(
												require_uint256(rayMulCVL(scaledBalanceOf(recipient), index)),
												require_uint256(recipientDiscountTokenBalance + amount)
											));

	mathint discountPercentRecipientAfter = getDiscountPercent(recipient);

	assert discountPercentRecipientAfter == estimatedDiscountPercentSender;
}

//pass
/**
* @title proves that updateDiscountDistribution updates scaled balance for sender.
**/
rule integrityOfUpdateDiscountDistribution_burnCorrectAmount_sender(
	env e,
	address sender,
    address recipient,
    uint256 senderDiscountTokenBalance,
    uint256 recipientDiscountTokenBalance,
    uint256 amount
) {
	address target; // SENDER
	require scaledBalanceOf(recipient) == 0; // ignore recipient branch coz timeout
	require target == sender;

	uint256 index = indexAtTimestamp(e.block.timestamp);

	uint256 scaledBalanceBefore = scaledBalanceOf(target);

	uint256 discountPercent = getDiscountPercent(target);

	require scaledBalanceBefore != 0;

	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(target, scaledBalanceBefore, discountPercent, index);

	// restrict path
	require balanceIncrease != 0;
	require discountPercent != 0;

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	uint256 scaledBalanceAfter = scaledBalanceOf(target);
	assert scaledBalanceAfter + require_uint128(discountScaled) == to_mathint(scaledBalanceBefore);
	//assert scaledBalanceAfter <= scaledBalanceBefore;
	// TODO prove in other rule:
	//assert scaledBalanceBefore == 0 => scaledBalanceAfter == scaledBalanceBefore;
	//assert scaledBalanceAfter + discountScaled == to_mathint(scaledBalanceBefore);
}

//pass
/**
* @title proves that updateDiscountDistribution updates scaled balance for recipient.
**/
rule integrityOfUpdateDiscountDistribution_burnCorrectAmount_recipient(
	env e,
	address sender,
    address recipient,
    uint256 senderDiscountTokenBalance,
    uint256 recipientDiscountTokenBalance,
    uint256 amount
) {
	address target; // RECIPIENT
	require scaledBalanceOf(sender) == 0; // ignore sender branch coz timeout
	require target == recipient;

	uint256 index = indexAtTimestamp(e.block.timestamp);

	uint256 scaledBalanceBefore = scaledBalanceOf(target);

	uint256 discountPercent = getDiscountPercent(target);

	require scaledBalanceBefore != 0;

	mathint balanceIncrease; mathint discountScaled;
	balanceIncrease, discountScaled = getBalanceIncreaseAndDiscountScaled(target, scaledBalanceBefore, discountPercent, index);

	// restrict path
	require balanceIncrease != 0;
	require discountPercent != 0;

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	uint256 scaledBalanceAfter = scaledBalanceOf(target);
	assert scaledBalanceAfter + require_uint128(discountScaled) == to_mathint(scaledBalanceBefore);
}

//pass
/**
* @title proves that updateDiscountDistribution doesnt change scaledBalance when both zero.
**/
rule integrityOfUpdateDiscountDistribution_burnCorrectAmount_none(
	env e,
	address sender,
    address recipient,
    uint256 senderDiscountTokenBalance,
    uint256 recipientDiscountTokenBalance,
    uint256 amount
) {
	address target; // SENDER or RECIPIENT
	require target == sender || target == recipient;
	// NONE
	require scaledBalanceOf(sender) == 0;
	require scaledBalanceOf(recipient) == 0;
	require target == sender || target == recipient;

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	uint256 scaledBalanceAfter = scaledBalanceOf(target);
	assert scaledBalanceAfter == 0;
}

// rule integrityOfUpdateDiscountDistribution_burnCorrectAmountCVL(
// 	env e,
// 	address sender,
//     address recipient,
//     uint256 senderDiscountTokenBalance,
//     uint256 recipientDiscountTokenBalance,
//     uint256 amount
// ) {
// 	address target; // RECIPIENT
// 	require scaledBalanceOf(sender) == 0;
// 	require target == recipient;

// 	uint256 index = indexAtTimestamp(e.block.timestamp);

// 	uint256 scaledBalanceBefore = scaledBalanceOf(target);

// 	uint256 discountPercent = getDiscountPercent(target);

// 	require scaledBalanceBefore != 0;


// 	mathint balanceIncreaseCVL_tmp = rayMulCVL(scaledBalanceBefore, index) - rayMulCVL(scaledBalanceBefore, getUserCurrentIndex(target));

// 	require balanceIncreaseCVL_tmp != 0;
// 	require discountPercent != 0;

// 	mathint discount = percentMulCVL(require_uint256(balanceIncreaseCVL_tmp), discountPercent);

// 	mathint discountScaledCVL = rayDivCVL(require_uint256(discount), index);
// 	mathint balanceIncreaseCVL = balanceIncreaseCVL_tmp - discount;

// 	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

// 	uint256 scaledBalanceAfter = scaledBalanceOf(target);
// 	assert scaledBalanceAfter + require_uint128(discountScaledCVL) == to_mathint(scaledBalanceBefore);
// 	//assert scaledBalanceAfter <= scaledBalanceBefore;
// 	// TODO prove in other rule:
// 	//assert scaledBalanceBefore == 0 => scaledBalanceAfter == scaledBalanceBefore;
// 	//assert scaledBalanceAfter + discountScaled == to_mathint(scaledBalanceBefore);
// }

/***************************************************************
* Integrity of rebalanceUserDiscountPercent
***************************************************************/

/**
* @title proves that after calling rebalanceUserDiscountPercent, the user's discount rate is up to date
**/
rule integrityOfRebalanceUserDiscountPercent_updateDiscountRate() {
	address user;
	env e;
	rebalanceUserDiscountPercent(e, user);
	assert(discStrategy.calculateDiscountRate(balanceOf(e, user), getBalanceOfDiscountToken(e, user)) == getUserDiscountRate(user));
}

/**
* @title proves that after calling rebalanceUserDiscountPercent, the user's state is updated with the recent index value
**/
rule integrityOfRebalanceUserDiscountPercent_updateIndex() {
	address user;
	env e;
	rebalanceUserDiscountPercent(e, user);
	uint256 index = indexAtTimestamp(e.block.timestamp);
	assert(getUserCurrentIndex(user) == index);
}

/**
* @title proves that rebalanceUserDiscountPercent can't effect other user's scaled balance
**/
// pass
rule integrityOfRebalanceUserDiscountPercent_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	address targetUser;
	rebalanceUserDiscountPercent(e, targetUser);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}

/***************************************************************
* Integrity of balanceOf
***************************************************************/

/**
* @title proves that a user with 100% discounts has a fixed balance over time
**/
rule integrityOfBalanceOf_fullDiscount() {
	address user;
	uint256 fullDiscountRate = 10000; //100%
	require(getUserDiscountRate(user) == fullDiscountRate);
	env e1;
	env e2;
	uint256 index1 = indexAtTimestamp(e1.block.timestamp);
	uint256 index2 = indexAtTimestamp(e2.block.timestamp);
	assert(balanceOf(e1, user) == balanceOf(e2, user));
}

/**
* @title proves that a user's balance, with no discount, is equal to rayMul(scaledBalance, current index)
**/
rule integrityOfBalanceOf_noDiscount() {
	address user;
	require(getUserDiscountRate(user) == 0);
	env e;
	uint256 scaledBalance = scaledBalanceOf(user);
	uint256 currentIndex = indexAtTimestamp(e.block.timestamp);
	mathint expectedBalance = rayMulCVL(scaledBalance, currentIndex);
	assert(to_mathint(balanceOf(e, user)) == expectedBalance);
}

/**
* @title proves the a user with zero scaled balance has a zero balance
**/
rule integrityOfBalanceOf_zeroScaledBalance() {
	address user;
	env e;
	uint256 scaledBalance = scaledBalanceOf(user);
	require(scaledBalance == 0);
	assert(balanceOf(e, user) == 0);
}

rule burnAllDebtReturnsZeroDebt(address user) {
    env e;
	uint256 _variableDebt = balanceOf(e, user);
	burn(e, user, _variableDebt, indexAtTimestamp(e.block.timestamp));
	uint256 variableDebt_ = balanceOf(e, user);
    assert(variableDebt_ == 0);
}

// Access control rules
// onlyPoolAdmin

/**
* @title The incentivesController address(`_incentivesController`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule incentivesControllerCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> f.selector != sig:initialize(address, address, address, uint8, string, string, bytes).selector
	  && !functionsThatRevert(f)
} {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address incentivesControllerBefore = getIncentivesController();

	f(e, args);

	address incentivesControllerAfter = getIncentivesController();

	assert !isAdmin => incentivesControllerAfter == incentivesControllerBefore;
	assert (isAdmin && (incentivesControllerAfter != incentivesControllerBefore)) => (f.selector == sig:setIncentivesController(address).selector);
}

/**
* @title The discountRateStrategy address(`_discountRateStrategy`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule discountRateStrategyCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> f.selector != sig:initialize(address, address, address, uint8, string, string, bytes).selector
	  && !functionsThatRevert(f)
} {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address discountRateStrategyBefore = getDiscountRateStrategy();

	f(e, args);

	address discountRateStrategyAfter = getDiscountRateStrategy();

	assert !isAdmin => discountRateStrategyAfter == discountRateStrategyBefore;
	assert (isAdmin && (discountRateStrategyAfter != discountRateStrategyBefore)) => (f.selector == sig:updateDiscountRateStrategy(address).selector);
}

/**
* @title The discountToken address(`_discountToken`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule discountTokenCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> f.selector != sig:initialize(address, address, address, uint8, string, string, bytes).selector
	  && !functionsThatRevert(f)
} {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address discountTokenBefore = getDiscountToken();

	f(e, args);

	address discountTokenAfter = getDiscountToken();

	assert !isAdmin => discountTokenAfter == discountTokenBefore;
	assert (isAdmin && (discountTokenAfter != discountTokenBefore)) => (f.selector == sig:updateDiscountToken(address).selector);
}
// //_ghoAToken

/**
* @title The ghoAToken address(`_ghoAToken`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule ghoATokenCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> f.selector != sig:initialize(address, address, address, uint8, string, string, bytes).selector
	  && !functionsThatRevert(f)
} {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address ghoATokenBefore = getAToken();

	f(e, args);

	address ghoATokenAfter = getAToken();

	assert !isAdmin => ghoATokenAfter == ghoATokenBefore;
	assert (isAdmin && (ghoATokenAfter != ghoATokenBefore)) => (f.selector == sig:setAToken(address).selector);
}


/**
* @title Only discount token address(`onlyDiscountToken`) can call updateDiscountDistribution.
*/
rule onlyDiscountTokenCanCall(
	env e,
	calldataarg args
) {
	require e.msg.sender != getDiscountToken();
	updateDiscountDistribution@withrevert(e, args);
	assert lastReverted;
}

/**
* @title A users anyAccumulatedDebtInteres (`_ghoUserState[user].accumulatedDebtInterest`) value can only be decreased by the AToken contract.
*/
rule onlyATokenCanDecreaseAccumulatedDebtInterest(
	env e,
	method f,
	calldataarg args,
	address anyUser
)
	filtered { f -> !functionsThatRevert(f) }
{
	mathint anyAccumulatedDebtInterestBefore = getBalanceFromInterest(anyUser);
	f(e, args);
	mathint anyAccumulatedDebtInterestAfter = getBalanceFromInterest(anyUser);

	assert (anyAccumulatedDebtInterestAfter < anyAccumulatedDebtInterestBefore) => (e.msg.sender == getAToken());
}

/**
* @title mint and burn can only be called by the pool.
*/
rule functionsOnlyCalledByPool(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> f.selector == sig:mint(address, address, uint256, uint256).selector
	  || f.selector == sig:burn(address, uint256, uint256).selector
} {
	bool msgSenderIsPool = (e.msg.sender == POOL());

	f(e, args);

	assert msgSenderIsPool;
}

ghost bool initializing_ghost;
hook Sload bool init currentContract.initializing STORAGE {
    require initializing_ghost == init;
}

ghost uint256 lastInitializedRevision_ghost;
hook Sload uint256 lastRev currentContract.lastInitializedRevision STORAGE {
	require lastInitializedRevision_ghost == lastRev;
}

ghost bool isConstructor_ghost;
function isConstructorFromGhost() returns bool {
	return isConstructor_ghost;
}

/**
* @title initialize() sets values correctly and reverts when expected.
*/
rule initializeCorrectness(
	env e,
	address initializingPool,
    address underlyingAsset,
    address incentivesController,
    uint8 debtTokenDecimals,
    string debtTokenName,
    string debtTokenSymbol,
    bytes params
) {
	bool initializerBefore = initializing_ghost || isConstructor_ghost || DEBT_TOKEN_REVISION() > lastInitializedRevision_ghost;

	initialize(e, initializingPool, underlyingAsset, incentivesController, debtTokenDecimals, debtTokenName, debtTokenSymbol, params);

	assert initializerBefore; // check revert
	assert initializingPool == POOL(); // check revert

	assert debtTokenDecimals == decimals();
	//assert debtTokenName == name();
	//assert debtTokenSymbol == symbol();
	assert underlyingAsset == UNDERLYING_ASSET_ADDRESS();
	assert incentivesController == getIncentivesController();
	// domainSep
}

/**
* @title Only initialize() can set UNDERLYING_ASSET_ADDRESS.
*/
rule underlyingAssetOnlySetByInitialize(
	env e,
	method f,
	calldataarg args
) filtered { f -> !functionsThatRevert(f) } {
	address underlyingAssetBefore = UNDERLYING_ASSET_ADDRESS();

	f(e, args);

	address underlyingAssetAfter = UNDERLYING_ASSET_ADDRESS();

	assert underlyingAssetAfter != underlyingAssetBefore => f.selector == sig:initialize(address, address, address, uint8, string, string, bytes).selector;
}

/**
* @title setAToken() sets value correctly. setAToken can only be called by admin when not set yet.
*/
rule setATokenCorrectness(
	env e,
	address ghoAToken
) {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address ghoATokenBefore = getAToken();

	setAToken@withrevert(e, ghoAToken);
	bool setATokenReverted = lastReverted;


	address ghoATokenAfter = getAToken();

	assert !isAdmin => setATokenReverted;
	assert (ghoATokenBefore != 0) => setATokenReverted;
	assert (ghoAToken == 0) => setATokenReverted;
	assert !setATokenReverted => (ghoATokenAfter == ghoAToken);
}

/**
* @title updateDiscountRateStrategy() sets value correctly. updateDiscountRateStrategy can only be called by pool admin.
*/
rule updateDiscountRateStrategyCorrectness(
	env e,
	address newDiscountRateStrategy
) {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];

	updateDiscountRateStrategy(e, newDiscountRateStrategy);
	bool updateDiscountRateStrategyReverted = lastReverted;

	address discountRateStrategyAfter = getDiscountRateStrategy();

	assert !isAdmin => updateDiscountRateStrategyReverted;
	assert (newDiscountRateStrategy == 0) => updateDiscountRateStrategyReverted;
	assert !updateDiscountRateStrategyReverted => (discountRateStrategyAfter == newDiscountRateStrategy);
}

/**
* @title updateDiscountToken() sets value correctly. updateDiscountToken can only be called by pool admin.
*/
rule updateDiscountTokenCorrectness(
	env e,
	address newDiscountToken
) {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];

	updateDiscountToken(e, newDiscountToken);
	bool updateDiscountTokenReverted = lastReverted;

	address discountTokenAfter = getDiscountToken();

	assert !isAdmin => updateDiscountTokenReverted;
	assert (newDiscountToken == 0) => updateDiscountTokenReverted;
	assert !updateDiscountTokenReverted => (discountTokenAfter == newDiscountToken);
}

/**
* @title decreaseBalanceFromInterest() decreases accumulatedIntrest by correct amount and only be called by the AToken contract.
*/
rule decreaseBalanceFromInterestCorrectness(
	env e,
	address user,
	uint256 amount
) {
	mathint accumulatedInterestBefore = getUserAccumulatedDebtInterest(user);

	decreaseBalanceFromInterest@withrevert(e, user, amount);
	bool decreaseBalanceFromInterestReverted = lastReverted;

	mathint accumulatedInterestAfter = getUserAccumulatedDebtInterest(user);

	assert (e.msg.sender != getAToken()) => decreaseBalanceFromInterestReverted;
	assert !decreaseBalanceFromInterestReverted => (to_mathint(assert_uint128(accumulatedInterestAfter + amount)) == accumulatedInterestBefore);
}
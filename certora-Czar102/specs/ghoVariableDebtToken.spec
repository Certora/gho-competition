import "VariableDebtToken.spec";

using GhoDiscountRateStrategy as discStrategy;
using DummyERC20WithTimedBalanceOf as discountToken;
using DummyPool as pool;
using GhoTokenHelper as GhoTokenHelper;

methods{
	
  	/***********************************;
    *    PoolAddressesProvider.sol     *;
    ************************************/
	function _.getACLManager() external => CONSTANT;

	/************************;
    *    ACLManager.sol     *;
    *************************/
	function _.isPoolAdmin(address) external => CONSTANT;

	/******************************************************************;
	*	DummyERC20WithTimedBalanceOf.sol (linked to _discountToken)   *;
	*******************************************************************/
	// represent a random balance per block 
	function discountToken.balanceOf(address user) external returns (uint256) with (env e) => balanceOfDiscountTokenAtTimestamp(user, e.block.timestamp);

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

	/********************************;
	*	GhoVariableDebtToken.sol	*;
	*********************************/
	function totalSupply() external returns(uint256);
	function balanceOf(address) external returns (uint256);
	function mint(address, address, uint256, uint256) external returns (bool, uint256);
	function burn(address ,uint256 ,uint256) external returns (uint256);
	function scaledBalanceOf(address) external returns (uint256) envfree;
	function getBalanceFromInterest(address) external returns (uint256) envfree;
	function rebalanceUserDiscountPercent(address) external;
	function updateDiscountDistribution(address ,address ,uint256 ,uint256 ,uint256) external;
	function POOL() external returns (address) envfree;
	function UNDERLYING_ASSET_ADDRESS() external returns (address) envfree;
	function DOMAIN_SEPARATOR() external returns (bytes32) envfree;
	function getIncentivesController() external returns (address) envfree;
	function name() external returns (string) envfree;
	function symbol() external returns (string) envfree;
	function decimals() external returns (uint8) envfree;
	function getDiscountToken() external returns (address) envfree;

	function accrueDebt(address user) external returns (uint256,uint256);
	function refreshDiscountPercent(address user, uint256 discountTokenBalance) external;

	function GhoTokenHelper.areStringsSame(string,string) external returns (bool) envfree;
	function GhoTokenHelper.compare(string,string) external returns (bool) envfree;

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
function percentMulCVL(uint256 a, uint256 b) returns mathint {
	return ((a * b + 5000) / 10000);
}


//todo: check balanceof after mint (stable index), burn after balanceof

definition MAX_DISCOUNT() returns uint256 = 10000; // equals to 100% discount, in points

ghost mapping(address => mapping (uint256 => uint256)) discount_ghost;
ghost mapping(uint256 => uint256) index_ghost;

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

/**
* @title at any point in time, the user's discount rate isn't larger than 100%
**/
invariant discountCantExceed100Percent(address user)
	getUserDiscountRate(user) <= MAX_DISCOUNT()
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
rule nonMintFunctionCantIncreaseBalance(method f) filtered { f-> f.selector != sig:mint(address, address, uint256, uint256).selector } {
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
rule nonMintFunctionCantIncreaseScaledBalance(method f) filtered { f-> f.selector != sig:mint(address, address, uint256, uint256).selector } {
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
rule debtTokenIsNotTransferable(method f) {
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
rule onlyCertainFunctionsCanModifyScaledBalance(method f) {
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
rule userAccumulatedDebtInterestWontDecrease(method f) {
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
rule userCantNullifyItsDebt(method f) {
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


//pass
use rule integrityMint_atoken;

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

/**
* @title Proves that after burning all debt, the debt is zero.
**/
rule burnAllDebtReturnsZeroDebt(address user) {
    env e;
	uint256 _variableDebt = balanceOf(e, user);
	burn(e, user, _variableDebt, indexAtTimestamp(e.block.timestamp));
	uint256 variableDebt_ = balanceOf(e, user);
    assert(variableDebt_ == 0);
}

function mustRevert(method f) returns bool {
	return !(f.selector != sig:allowance(address,address).selector &&
		f.selector != sig:approve(address,uint256).selector &&
		f.selector != sig:increaseAllowance(address,uint256).selector &&
		f.selector != sig:decreaseAllowance(address,uint256).selector &&
		f.selector != sig:transfer(address,uint256).selector &&
		f.selector != sig:transferFrom(address,address,uint256).selector);
}

/**
* @title proves that there are scenarios in which each implemented function succeeds
**/
rule noRevertInScenarios(method f) {
	calldataarg arg; env e;
	f@withrevert(e, arg);
	satisfy !lastReverted || mustRevert(f), "Function always reverts";
}

/**
* @title Prove that for always reverting functions they always revert
**/
rule revertingMustRevert(method f) {
	calldataarg arg; env e;
	f@withrevert(e, arg);
	assert lastReverted || !mustRevert(f), "Function doesn't always revert";
}

// rule noRevertInScenarios(method f) filtered {
// 	f-> f.selector != sig:allowance(address,address).selector &&
// 		f.selector != sig:approve(address,uint256).selector &&
// 		f.selector != sig:increaseAllowance(address,uint256).selector &&
// 		f.selector != sig:decreaseAllowance(address,uint256).selector &&
// 		f.selector != sig:transfer(address,uint256).selector &&
// 		f.selector != sig:transferFrom(address,address,uint256).selector
// } {
// 	calldataarg arg; env e;
// 	f(e, arg);
// 	satisfy !lastReverted, "Function always reverts";
// }

ghost uint lastInitializedRevisionGhost {
	init_state axiom lastInitializedRevisionGhost == 0;
}

hook Sload uint value lastInitializedRevision STORAGE {
	require lastInitializedRevisionGhost == value;
}

hook Sstore lastInitializedRevision uint value (uint old_value) STORAGE {
	require lastInitializedRevisionGhost == old_value;
	lastInitializedRevisionGhost = value;
}

/**
* @title Makes sure that the revision is at most 1
**/
invariant revisionMax1()
	lastInitializedRevisionGhost <= 1;

ghost bool initializingGhost {
	init_state axiom !initializingGhost;
}

hook Sload bool value initializing STORAGE {
	require initializingGhost == value;
}

hook Sstore initializing bool value (bool old_value) STORAGE {
	initializingGhost = value;
}

/**
* @title Ensures that the initializing bool is always false outside of the execution context
**/
invariant integrityOfInitializing()
	!initializingGhost;

ghost uint nameFlag {
	init_state axiom nameFlag == 0;
}

hook Sload uint value _name.(offset 0) STORAGE {
	require nameFlag == value;
}

hook Sstore _name.(offset 0) uint value (uint old_value) STORAGE {
	nameFlag = value;
}

ghost uint symbolFlag {
	init_state axiom nameFlag == 0;
}

hook Sload uint value _symbol.(offset 0) STORAGE {
	require symbolFlag == value;
}

hook Sstore _symbol.(offset 0) uint value (uint old_value) STORAGE {
	symbolFlag = value;
}

/**
* @title Ensures the integrity of the name storage
**/
invariant nameStorageIntegrity()
	((nameFlag & 1 == 0) => ((nameFlag & 0xff) / 2 < 0x20)) &&
		((nameFlag & 1 == 1) => (nameFlag / 2 >= 0x20));

/**
* @title Ensures the integrity of the symbol storage
**/
invariant symbolStorageIntegrity()
	((symbolFlag & 1 == 0) => ((symbolFlag & 0xff) / 2 < 0x20)) &&
		((symbolFlag & 1 == 1) => (symbolFlag / 2 >= 0x20));

/**
* @title ensures the state change and revert reasons of the initialize() function are as intended
**/
rule initializeIntegrity() {
	calldataarg arg; env e;

	requireInvariant revisionMax1();
	requireInvariant integrityOfInitializing();
	requireInvariant nameStorageIntegrity();
	requireInvariant symbolStorageIntegrity();
	
	address _pool;
	address underlying;
	address ic;
	uint8 decimals;
	string symbol;
	string name;
	bytes params;

	require //symbol.length < 2 ^ 5 &&
		// name.length < 2 ^ 5 &&
		(name.length % 32) == 0 &&
		name.length <= 192 && 
		(symbol.length % 32) == 0 &&
		symbol.length <= 192 && 
		params.length < 2 ^ 5;

	uint prevRevision = lastInitializedRevisionGhost;
	
	initialize@withrevert(e, _pool, underlying, ic, decimals, name, symbol, params);
	bool reverted = lastReverted;

	assert (reverted => (
		_pool != POOL() ||
		prevRevision == 1 ||
		e.msg.value != 0
	)) && ((
		_pool != POOL() ||
		prevRevision == 1 ||
		e.msg.value != 0
	) => reverted);

	assert !reverted => (
		underlying == UNDERLYING_ASSET_ADDRESS() &&
		ic == getIncentivesController() &&
		decimals == decimals() &&
		GhoTokenHelper.areStringsSame(symbol, symbol()) &&
		GhoTokenHelper.areStringsSame(name, name()) &&
		DOMAIN_SEPARATOR() != to_bytes32(0)
	);
}

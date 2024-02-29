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
	function _.isPoolAdmin(address) external => CONSTANT;

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
* @title user balanceOf should not always revert if their current index is greater than that retrieved from the pool
**/
rule balanceOfUserShouldNotAlwaysRevertIfCurrentIndexIsGreaterThanPoolsIndex() {
    env e;
	
	address from;
    uint256 amount;
	uint256 index;

	uint256 discountPercent = getUserDiscountRate(from);

	require discountPercent > 0;
	require(getUserCurrentIndex(from) > currentIndex(e));
	
	balanceOf(e, from);
	satisfy true;
}

import "erc20.spec";

using GhoToken as GHOTOKEN;
using GhoTokenHelper as GhoTokenHelper;

methods{

	function totalSupply() external returns (uint256) envfree;
	function RESERVE_TREASURY_ADDRESS() external returns (address) envfree;
	function UNDERLYING_ASSET_ADDRESS() external returns (address) envfree;
	function transferUnderlyingTo(address,uint256) external;
	function handleRepayment(address,address,uint256) external; 
	function distributeFeesToTreasury() external envfree ;
	function rescueTokens(address,address,uint256) external; 
	function setVariableDebtToken(address)  external;
	function getVariableDebtToken() external returns (address) envfree;
	function updateGhoTreasury(address) external ;
	function getGhoTreasury() external returns (address) envfree;
	function scaledBalanceOf(address) external returns (uint256) envfree;
	/*******************
    *   GhoToken.sol   *
    ********************/
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns (uint256) envfree;
	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns (uint256) envfree;
	function GHOTOKEN.balanceOf(address) external returns (uint256) envfree;

	/************************************
    *   GhoTokenVariableDebtToken.sol   *
    *************************************/
	function _.getBalanceFromInterest(address user) external  => DISPATCHER(true);
	function _.decreaseBalanceFromInterest(address user, uint256 amount) external => DISPATCHER(true);


  	/*******************
    *     Pool.sol     *
    ********************/
    function _.getReserveNormalizedIncome(address) external => CONSTANT;


  	/***********************************
    *    PoolAddressesProvider.sol     *
    ************************************/
	function _.getACLManager() external => CONSTANT;

	/************************
    *    ACLManager.sol     *
    *************************/
	function _.isPoolAdmin(address) external => CONSTANT;



}

/**
* @title Proves that ghoAToken::mint always reverts
**/
rule noMint() {
	env e;
	calldataarg args;
	mint@withrevert(e, args);
	assert lastReverted;
}

/**
* @title Proves that ghoAToken::burn always reverts
**/
rule noBurn() {
	env e;
	calldataarg args;
	burn@withrevert(e, args);
	assert lastReverted;
}

/**
* @title Proves that ghoAToken::transfer always reverts
**/
rule noTransfer() {
	env e;
	calldataarg args;
	transfer@withrevert(e, args);
	assert lastReverted;
}


/** 
* @title Proves that calling ghoAToken::transferUnderlyingTo will revert if the amount exceeds the excess capacity  
* @notice A user can’t borrow more than the facilitator’s remaining capacity.
**/
rule transferUnderlyingToCantExceedCapacity() {
	address target;
	uint256 amount;
	env e;
	mathint facilitatorLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint facilitatorCapacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);
	transferUnderlyingTo@withrevert(e, target, amount);
	assert(to_mathint(amount) > (facilitatorCapacity - facilitatorLevel) => lastReverted);
}


/**
* @title Proves that the total supply of GhoAToken is always zero
**/
invariant totalSupplyAlwaysZero() 
	totalSupply() == 0;


/**
* @title Proves that any user's balance of GhoAToken is always zero
**/
invariant userBalanceAlwaysZero(address user)
	scaledBalanceOf(user) == 0;




/**
* @title BucketLevel decreases after transferUnderlyingTo() followed by handleRepayment()
* @dev repayment funds are, partially or fully, transferred to the treasury
*/
rule integrityTransferUnderlyingToWithHandleRepayment()
{
	env e;
	calldataarg arg;
	uint256 amount;
	address target;
	address user;
    address onBehalfOf;

	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	transferUnderlyingTo(e, target, amount);
	handleRepayment(e, user, onBehalfOf, amount);
	uint256 levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	assert levelBefore <= levelAfter;

}



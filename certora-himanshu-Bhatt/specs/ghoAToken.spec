using GhoToken as GHOTOKEN;
using GhoTokenHelper as GhoTokenHelper;
// using ACLManager as ACLManager;

methods{
	// erc20 methods
    function _.name() external                                 => DISPATCHER(true);
    function _.symbol() external                              => DISPATCHER(true);
    function _.decimals() external                            => DISPATCHER(true);
    function _.totalSupply() external                         => DISPATCHER(true);
    function _.balanceOf(address) external                    => DISPATCHER(true);
    function _.allowance(address,address) external            => DISPATCHER(true);
    function _.approve(address,uint256) external              => DISPATCHER(true);
    function _.transfer(address,uint256) external             => DISPATCHER(true);
    function _.transferFrom(address,address,uint256) external => DISPATCHER(true);

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
// latest run :- https://prover.certora.com/output/42902/69b004983e7744cea148fb479e3d554b/?anonymousKey=98296394d9f447e6b0dd8696174c3f797f453ac1
rule transferUnderlyingToCantExceedCapacity() {
	address target;
	uint256 amount;
	env e;
	mathint facilitatorLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint facilitatorCapacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);
	transferUnderlyingTo@withrevert(e, target, amount);
	assert(to_mathint(amount) > (facilitatorCapacity - facilitatorLevel) => lastReverted);
	assert !lastReverted=> e.msg.sender==pool_address(e);
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
// latest run :- https://prover.certora.com/output/42902/adec5f19c45944f6905b41a9158e5ecb/?anonymousKey=ea2020df1ddce576d12b2cc22d7bffa97b47e69d
rule handlePaymentIntegrity(){
	env e;address user;address onBehalfOf;uint256 amount;
	mathint _balanceFromInterest=getBalanceFromInterest_debt(e,onBehalfOf);

	mathint initialLvl=	GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint _balance=GHOTOKEN.balanceOf(e,currentContract);
	
	handleRepayment(e,user,onBehalfOf,amount);
	mathint finalLvl=GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balance_=GHOTOKEN.balanceOf(e,currentContract);

	mathint balanceFromInterest_=getBalanceFromInterest_debt(e,onBehalfOf);
	mathint diff=amount-_balanceFromInterest;
	
	assert e.msg.sender==pool_address(e);
	assert amount<=assert_uint256(_balanceFromInterest)=>balanceFromInterest_==(_balanceFromInterest-amount);
	assert amount > assert_uint256(_balanceFromInterest) => balanceFromInterest_==0 && finalLvl==initialLvl-(diff) && balance_==_balance-diff;

}



definition disAllowedFunctions(method f) returns bool = 
            f.selector == sig:burn(address,address,uint256,uint256).selector ||
            f.selector == sig:transferOnLiquidation(address,address,uint256).selector ||
            f.selector == sig:transferFrom(address,address,uint256).selector ||
            f.selector == sig:mintToTreasury(uint256,uint256).selector ||
            f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector ||
            f.selector == sig:transfer(address,uint256).selector ||
            f.selector == sig:mint(address,address,uint256,uint256).selector;
       


// https://prover.certora.com/output/42902/adc467e1a09a457b91a5c1b6240b9761/?anonymousKey=1d646fc80023f64b6410feb181b6d16598eeb326
rule onlyAdminChangeDebtToken(method f,env e,calldataarg args) filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address _a=getVariableDebtToken();
	f(e,args);
	address a_=getVariableDebtToken();
	assert _a!=a_ => is_pool_admin(e,e.msg.sender);
}
// https://prover.certora.com/output/42902/adc467e1a09a457b91a5c1b6240b9761/?anonymousKey=1d646fc80023f64b6410feb181b6d16598eeb326
rule onlyAdminUpdateTreasury(method f,env e,calldataarg args) filtered{f->!f.isView  && !disAllowedFunctions(f)}{
	address _a=getGhoTreasury();
	f(e,args);
	address a_=getGhoTreasury();
	assert _a!=a_ => is_pool_admin(e,e.msg.sender);
}

// https://prover.certora.com/output/42902/8c6474943df249b9b5fe5e64f9f4ddb0/?anonymousKey=7fd7c00ee360d2409e6347c56a511c8be8af402d
rule only_ghoTreasury_balance_increases(method f,env e,calldataarg args) filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;
	uint256 _b=GHOTOKEN.balanceOf(user);
	f(e,args);
	uint256 b_=GHOTOKEN.balanceOf(user);
	assert b_>_b => user==getGhoTreasury() || e.msg.sender==pool_address(e);
}

// https://prover.certora.com/output/42902/d22a915084344a988f00001fe9243f98/?anonymousKey=50a8fa1a7c4c1259989d222ae6918f25d2370711
rule onlyPool_call_transferUnderlyingTo(){
	env e;calldataarg args;
	transferUnderlyingTo@withrevert(e,args);
	assert !lastReverted => e.msg.sender==pool_address(e);
}
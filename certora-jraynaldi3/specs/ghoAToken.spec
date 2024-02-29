using GhoToken as GHOTOKEN;
using GhoTokenHelper as GhoTokenHelper;
using MockACLManager as ACLManager;
using MockAddressProvider as PoolAddressesProvider;
using DummyERC20A as TokenA;
using GhoVariableDebtToken as VariableDebtToken;
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
	function scaledTotalSupply() external returns (uint256) envfree;
	/**********************
    *   Public Variable   *
    ***********************/
	function POOL() external returns(address) envfree;
	function name() external returns(string) envfree;
	function decimals() external returns(uint8) envfree;
	function symbol() external returns(string) envfree;
	function getIncentivesController() external returns(address) envfree;
	function RESERVE_TREASURY_ADDRESS() external returns(address) envfree;
	function UNDERLYING_ASSET_ADDRESS() external returns(address) envfree;
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
	function VariableDebtToken.getBalanceFromInterest(address) external returns(uint256) envfree;

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
	function _.isPoolAdmin(address user) external => retreivePoolAdminFromGhost(user) expect bool ALL;

	/*********************
    *    DummyERC20A     *
    *********************/
	function DummyERC20A.balanceOf(address) external returns(uint256) envfree;


}

definition alwaysRevertFunction(method f) returns bool = (
	f.selector == sig:transferFrom(address,address,uint256).selector
	|| f.selector == sig:burn(address,address,uint256,uint256).selector
	|| f.selector == sig:mint(address,address,uint256,uint256).selector
	|| f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector
	|| f.selector == sig:mintToTreasury(uint256,uint256).selector
	|| f.selector == sig:transferOnLiquidation(address,address,uint256).selector
	|| f.selector == sig:transfer(address,uint256).selector
);

// keeps track of users with pool admin permissions in order to return a consistent value per user
ghost mapping(address => bool) poolAdmin_ghost;

// returns whether the user is a pool admin
function retreivePoolAdminFromGhost(address user) returns bool{
    return poolAdmin_ghost[user];
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
	scaledTotalSupply() == 0
	filtered {
		f -> !alwaysRevertFunction(f)
	}


/**
* @title Proves that any user's balance of GhoAToken is always zero
**/
invariant userBalanceAlwaysZero(address user)
	scaledBalanceOf(user) == 0
	filtered {
		f -> !alwaysRevertFunction(f)
	}




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

/********* Participant Defined Rules ***************/ 
// Several function should always revert 
rule functionReverted (
	env e,
	method f,
	calldataarg args
) {
	f@withrevert(e, args);
	assert alwaysRevertFunction(f) => lastReverted;
}

// everyfunction should atleast have one valid way without revert
// except that always revert function
rule satisfyFunctions(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> !alwaysRevertFunction(f)
}{
	f@withrevert(e, args);
	satisfy !lastReverted;
}

//only Pool can changed bucketLevel(mint or burn GhoToken)
rule onlyPool(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> !f.isView && !alwaysRevertFunction(f)
}{
	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	f(e,args);
	uint256 levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	assert levelBefore != levelAfter => e.msg.sender == POOL();
}

// only Pool Admin can change variable debt token and treasury
rule onlyPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> !f.isView && !alwaysRevertFunction(f)
} {
	//require ACLManager == PoolAddressesProvider.getACLManager(e);
	address treasuryBefore = getGhoTreasury();
	address variableDebtTokenBefore = getVariableDebtToken();
	bool isPoolAdmin = retreivePoolAdminFromGhost(e.msg.sender);
	f(e,args);
	address treasuryAfter = getGhoTreasury();
	address variableDebtTokenAfter = getVariableDebtToken();
	assert (treasuryAfter != treasuryBefore) || (variableDebtTokenAfter != variableDebtTokenBefore) => isPoolAdmin;
}

// cannot set addresses to address 0 
rule nonZeroVariable(
	env e,
	method f,
	calldataarg args
) filtered {
	f -> !f.isView && !alwaysRevertFunction(f)
}{
	address treasuryBefore = getGhoTreasury();
	address variableDebtTokenBefore = getVariableDebtToken();
	f(e,args);
	address treasuryAfter = getGhoTreasury();
	address variableDebtTokenAfter = getVariableDebtToken();

	assert variableDebtTokenAfter != variableDebtTokenBefore => variableDebtTokenBefore == 0 && variableDebtTokenAfter != 0;
	assert treasuryAfter != treasuryBefore => treasuryAfter != 0;
}

//initializing related hook 
ghost bool init;
hook Sload bool val currentContract.initializing STORAGE{
	require init == val;
}
hook Sstore currentContract.initializing bool val STORAGE{
	init = val;
}
//initializing should always false 
invariant initializingAlwaysFalse()
	init == false
	filtered {
		f -> !alwaysRevertFunction(f)
	}

//integrity of Initialize, only called once and set several variable
rule initialize_integrity(
	env e,
    address initializingPool,
    address treasury,
    address underlyingAsset,
    address incentivesController,
    uint8 aTokenDecimals,
    string aTokenName,
    string aTokenSymbol,
    bytes params
) {
	requireInvariant initializingAlwaysFalse();
	initialize@withrevert(
		e, 
		initializingPool,
		treasury,
		underlyingAsset,
		incentivesController,
		aTokenDecimals,
		aTokenName,
		aTokenSymbol,
		params
	);
	bool firstRevert = lastReverted;
	if (!firstRevert) {
	assert decimals() == aTokenDecimals;
	assert getIncentivesController() == incentivesController;
	assert RESERVE_TREASURY_ADDRESS() == treasury;
	assert UNDERLYING_ASSET_ADDRESS() == underlyingAsset;
	}
	assert initializingPool != POOL() => firstRevert;
}

//initialize should only called once
rule initialize_onlyOnce(
	env e,
	calldataarg args
) {
	requireInvariant initializingAlwaysFalse();
	initialize(e, args);
	initialize@withrevert(e,args);
	assert lastReverted;
}

//rescue token should capable to transfer any token except underlying assets 
rule rescueTokens_integrity (
	env e,
	address token,
	address to,
	uint256 amount
) {
	uint256 balanceBefore = TokenA.balanceOf(to);
	rescueTokens(e, token, to, amount);
	uint256 balanceAfter = TokenA.balanceOf(to);
	assert balanceAfter != balanceBefore 
		<=> token !=  UNDERLYING_ASSET_ADDRESS()
		&& token == TokenA
		&& amount != 0
		&& to != currentContract; 
}

// setVariableDebtToken should change _ghoVariableDebtToken
rule setVariableDebtToken_integrity (
	env e ,
	address variableDebtToken
) {
	address before = getVariableDebtToken();
	setVariableDebtToken(e, variableDebtToken);
	address after = getVariableDebtToken();
	assert after == variableDebtToken 
		<=> variableDebtToken != 0
		&& before == 0;
}

// updateGhoTreasury should change _ghoTreasury
rule updateGhoTreasury_integrity (
	env e,
	address treasury
) {
	address before = getGhoTreasury();
	updateGhoTreasury(e, treasury);
	address after = getGhoTreasury();
	assert after != before 
		<=> treasury != 0
		&& treasury != before;
}

// handleRepayment should decrease balance from interest and burn underlying assets if necessary
rule handleRepayment_integrity(
	env e,
	address user, 
	address onBehalfOf,
	uint256 amount
) {
	require user == 444; //simplification, user doesnt matter
	uint256 before = VariableDebtToken.getBalanceFromInterest(onBehalfOf);
	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	handleRepayment(e, user, onBehalfOf, amount);
	uint256 after = VariableDebtToken.getBalanceFromInterest(onBehalfOf);
	uint256 levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	assert amount <= before => before - after == to_mathint(amount);
	assert amount > before => after == 0 && levelBefore - levelAfter == amount - before; 
}

// handleRepayment should run while amount LT balanceFromInterest before
rule handleRepayment_satisfy1(
	env e, 
	address user, 
	address onBehalfOf,
	uint256 amount
) {
	require user == 444; //simplification, user doesnt matter
	uint256 before = VariableDebtToken.getBalanceFromInterest(onBehalfOf);
	require before > amount;
	handleRepayment@withrevert(e, user, onBehalfOf, amount);
	satisfy !lastReverted;
}

// handleRepayment should run while amount GT balanceFromInterest before
rule handleRepayment_satisfy2(
	env e, 
	address user, 
	address onBehalfOf,
	uint256 amount
) {
	require user == 444; //simplification, user doesnt matter
	uint256 before = VariableDebtToken.getBalanceFromInterest(onBehalfOf);
	require before < amount;
	handleRepayment@withrevert(e, user, onBehalfOf, amount);
	satisfy !lastReverted;
}

// distributeFeesToTreasury should transfer underlyingAsset to treasury 
rule distributeFeesToTreasury_integrity(
	env e
) {
	address treasury = getGhoTreasury();
	require treasury != currentContract;
	uint256 thisBalanceBefore = GHOTOKEN.balanceOf(currentContract);
	uint256 treasuryBalanceBefore = GHOTOKEN.balanceOf(treasury);
	require thisBalanceBefore + treasuryBalanceBefore < max_uint;

	distributeFeesToTreasury(e);

	uint256 thisBalanceAfter = GHOTOKEN.balanceOf(currentContract);
	uint256 treasuryBalanceAfter = GHOTOKEN.balanceOf(treasury);

	assert thisBalanceAfter == 0 ;
	assert treasuryBalanceAfter - treasuryBalanceBefore == to_mathint(thisBalanceBefore);
}

// cannot transfer GhoToken to other address than treasury
rule onlyTreasuryCanReceiveGhoToken(
	env e,
	method f,
	calldataarg args,
	address addr
) filtered {
	f -> !f.isView && !alwaysRevertFunction(f)
} {
	require addr != currentContract;
	address treasury = getGhoTreasury();
	uint256 thisBalanceBefore = GHOTOKEN.balanceOf(currentContract);
	uint256 addrBalanceBefore = GHOTOKEN.balanceOf(addr);

	f(e,args);

	uint256 thisBalanceAfter = GHOTOKEN.balanceOf(currentContract);
	uint256 addrBalanceAfter = GHOTOKEN.balanceOf(addr);
	assert thisBalanceAfter != thisBalanceBefore 
		&& addrBalanceAfter != addrBalanceBefore 
		=> f.selector == sig:distributeFeesToTreasury().selector
		&& treasury == addr;
}
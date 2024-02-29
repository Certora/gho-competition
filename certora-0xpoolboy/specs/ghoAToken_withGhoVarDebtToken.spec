using GhoToken as GHOTOKEN;
using GhoTokenHelper as GhoTokenHelper;
using GhoATokenHelper as GhoATokenHelper;
using GhoVariableDebtToken as GhoVariableDebtToken;

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
	function POOL() external returns (address) envfree;
	function ATOKEN_REVISION() external returns (uint256) envfree;
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
	function GHOTOKEN.totalSupply() external returns (uint256) envfree;

	function decimals() external returns (uint8) envfree;

	function VersionedInitializable.isConstructor() internal returns (bool) => isConstructorFromGhost();

	function getIncentivesController() external returns (address) envfree;

	/************************************
    *   GhoTokenVariableDebtToken.sol   *
    *************************************/
	//function _.getBalanceFromInterest(address user) external  => DISPATCHER(true);
	//function _.decreaseBalanceFromInterest(address user, uint256 amount) external => DISPATCHER(true);


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

// an assumption that demands the sum of balances of 3 given users is no more than the total supply
function ghoBalanceOfTwoUsersLETotalSupply(address user1, address user2, address user3){
    require GHOTOKEN.balanceOf(user1) + GHOTOKEN.balanceOf(user2) + GHOTOKEN.balanceOf(user3) <= to_mathint(GHOTOKEN.totalSupply());
}

definition functionsThatRevert(method f) returns bool =
	 ( f.selector == sig:mint(address, address, uint256, uint256).selector
	|| f.selector == sig:mintToTreasury(uint256, uint256).selector
	|| f.selector == sig:transferOnLiquidation(address, address, uint256).selector
	|| f.selector == sig:permit(address, address, uint256, uint256, uint8, bytes32, bytes32).selector
	|| f.selector == sig:transfer(address, uint256).selector
	|| f.selector == sig:transferFrom( address, address, uint256).selector
	|| f.selector == sig:burn(address, address, uint256, uint256).selector);


rule functionsShouldRevert(
	env e,
	method f,
	calldataarg args
) filtered { f -> functionsThatRevert(f) } {
	f@withrevert(e, args);
	assert lastReverted;
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
	totalSupply() == 0
	filtered {
		f -> !functionsThatRevert(f)
	}

/**
* @title Proves that any user's balance of GhoAToken is always zero
**/
invariant userBalanceAlwaysZero(address user)
	scaledBalanceOf(user) == 0
	filtered {
		f -> !functionsThatRevert(f)
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

/**
* @title The ReserveTreasury address(`_ghoTreasury`) can only be changed by a msg.sender holding the PoolAdmin role.
* @dev This rule relies on the `isPoolAdmin() => CONSTANT` summary.
*/
rule reserveTreasuryAddressCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
)
	filtered { f -> f.selector != sig:initialize(address, address, address, address, uint8, string, string, bytes).selector && !functionsThatRevert(f)}
{
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);
	address reserveTreasuryBefore = RESERVE_TREASURY_ADDRESS();

	f(e, args);

	address reserveTreasuryAfter = RESERVE_TREASURY_ADDRESS();

	assert !isAdmin => reserveTreasuryAfter == reserveTreasuryBefore;
}

/**
* @title The underlyingAsset adddres(`_underlyingAsset`) can only be changed by a msg.sender holding the PoolAdmin role.
* @dev This rule relies on the `isPoolAdmin() => CONSTANT` summary.
*/
rule underLyingAssetAddressCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
)
	filtered { f -> f.selector != sig:initialize(address, address, address, address, uint8, string, string, bytes).selector && !functionsThatRevert(f)}
{
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);
	address underLyingAssetBefore = UNDERLYING_ASSET_ADDRESS();

	f(e, args);

	address underLyingAssetAfter = UNDERLYING_ASSET_ADDRESS();

	assert !isAdmin => underLyingAssetAfter == underLyingAssetBefore;
}

/**
* @title The variableDebtToken address(`_ghoVariableDebtToken`) can only be changed by a msg.sender holding the PoolAdmin role.
* @dev This rule relies on the `isPoolAdmin() => CONSTANT` summary.
*/
rule ghoVariableDebtTokenCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
)
	filtered { f -> f.selector != sig:initialize(address, address, address, address, uint8, string, string, bytes).selector && !functionsThatRevert(f)}
{
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);
	address ghoVariableDebtTokenBefore = getVariableDebtToken();

	f(e, args);

	address ghoVariableDebtTokenAfter = getVariableDebtToken();

	assert !isAdmin => ghoVariableDebtTokenAfter == ghoVariableDebtTokenBefore;
}

// FIXME timeout
rule setVariableDebtTokenCorrectness(
	env e,
	address ghoVariableDebtToken
) {
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);
	address ghoVariableDebtTokenBefore = getVariableDebtToken();

	setVariableDebtToken(e, ghoVariableDebtToken);
	bool setVariableDebtTokenReverted = lastReverted;

	address ghoVariableDebtTokenAfter = getVariableDebtToken();

	assert ghoVariableDebtToken == 0 => setVariableDebtTokenReverted;
	assert ghoVariableDebtTokenBefore != 0 => setVariableDebtTokenReverted;
	assert !isAdmin => setVariableDebtTokenReverted;
	assert !setVariableDebtTokenReverted => ghoVariableDebtTokenAfter == ghoVariableDebtToken;
}

/**
* @title The ghoTreasury address(`_ghoTreasury`) can only be changed by a msg.sender holding the PoolAdmin role.
* @dev This rule relies on the `isPoolAdmin() => CONSTANT` summary.
*/
rule ghoTreasuryCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) filtered { f ->
	f.selector != sig:initialize(address, address, address, address, uint8, string, string, bytes).selector
	&& !functionsThatRevert(f) /* see rule: functionsShouldRevert */
	&& f.selector != sig:setVariableDebtToken(address).selector /* FIXME: This function causes timeout, but should be tested. */
} {
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);
	address ghoTreasuryBefore = getGhoTreasury();

	f(e, args);

	address ghoTreasuryAfter = getGhoTreasury();

	assert !isAdmin => ghoTreasuryAfter == ghoTreasuryBefore;
	assert isAdmin && ghoTreasuryAfter != ghoTreasuryBefore => f.selector == sig:updateGhoTreasury(address).selector && ghoTreasuryAfter != 0;
}

rule updateGhoTreasuryCorrectness(
	env e,
	address newGhoTreasury
) {
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);

	updateGhoTreasury@withrevert(e, newGhoTreasury);
	bool updateGhoTreasuryReverted = lastReverted;

	address ghoTreasuryAfter = getGhoTreasury();

	assert ((newGhoTreasury == 0) || !isAdmin) => updateGhoTreasuryReverted;
	assert !updateGhoTreasuryReverted => (ghoTreasuryAfter == newGhoTreasury);
}

/**
* @title `rescueTokens()` should revert when called without the pool admin role or when a rug pulled is attempted.
*/
rule rescueTokensRevertCorrectness(
	env e,
	address token,
	address to,
	uint256 amount
) {
	bool isAdmin = GhoATokenHelper.isPoolAdmin(e, e.msg.sender);

	rescueTokens@withrevert(e, token, to, amount);
	bool rescueTokensReverted = lastReverted;

	assert !isAdmin => rescueTokensReverted;
	assert (token == UNDERLYING_ASSET_ADDRESS()) => rescueTokensReverted;
}

/**
* @title `handleRepayment()` should adjust value correctly.
*/
rule handleRepaymentCorrectness(
	env e,
	address user,
    address onBehalfOf,
    uint256 amount
) {
	mathint balanceFromInterestBefore = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);
	mathint levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	handleRepayment(e, user, onBehalfOf, amount);

	mathint levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	assert (to_mathint(amount) <= balanceFromInterestBefore)
		=> (balanceFromInterestAfter + amount == balanceFromInterestBefore);
	assert (to_mathint(amount) > balanceFromInterestBefore)
		=> (balanceFromInterestAfter == 0);
	assert (to_mathint(amount) > balanceFromInterestBefore)
		=> (levelAfter + amount - balanceFromInterestBefore == levelBefore);
}

rule handleRepaymentCorrectness_conditionalSatisfiability1(
	env e,
	address user,
    address onBehalfOf,
    uint256 amount
) {
	ghoBalanceOfTwoUsersLETotalSupply(currentContract, e.msg.sender, user);
	mathint balanceFromInterestBefore = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);
	mathint levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	handleRepayment(e, user, onBehalfOf, amount);

	mathint levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	satisfy (to_mathint(amount) < balanceFromInterestBefore);
}

rule handleRepaymentCorrectness_conditionalSatisfiability2(
	env e,
	address user,
    address onBehalfOf,
    uint256 amount
) {
	ghoBalanceOfTwoUsersLETotalSupply(currentContract, e.msg.sender, user);
	mathint balanceFromInterestBefore = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);
	mathint levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	handleRepayment(e, user, onBehalfOf, amount);

	mathint levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	satisfy (to_mathint(amount) > balanceFromInterestBefore);
}
/**
* @title `handleRepayment()`.
*/
rule linearityOfHandleRepayment(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount1,
	uint256 amount2
) {
	mathint balanceFromInterestBefore = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);
	mathint levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	storage initState = lastStorage;

	handleRepayment(e, user, onBehalfOf, require_uint256(amount1));
	handleRepayment(e, user, onBehalfOf, require_uint256(amount2));
	mathint levelAfter_2 = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter_2 = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	handleRepayment(e, user, onBehalfOf, require_uint256(amount1+amount2)) at initState;
	mathint levelAfter_1 = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter_1 = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	assert levelAfter_2 == levelAfter_1;
	assert balanceFromInterestAfter_2 == balanceFromInterestAfter_1;
}

/**
* @title `distributeFeesToTreasury()` should empty the current contract and transfer that amount to the ghoTreasury.
*/
rule distributeFeesToTreasuryCorrectness(
) {
	address ghoTreasury = getGhoTreasury();
	address other;
	require ghoTreasury != currentContract;
	require other != currentContract && other != ghoTreasury;
	ghoBalanceOfTwoUsersLETotalSupply(currentContract, ghoTreasury, other);

	mathint feesToDistribute = GHOTOKEN.balanceOf(currentContract);
	mathint ghoTreasuryBalanceBefore = GHOTOKEN.balanceOf(ghoTreasury);

	distributeFeesToTreasury();

	mathint balanceAfter = GHOTOKEN.balanceOf(currentContract);
	mathint ghoTreasuryBalanceAfter = GHOTOKEN.balanceOf(ghoTreasury);

	assert balanceAfter == 0;
	assert ghoTreasuryBalanceAfter == ghoTreasuryBalanceBefore + feesToDistribute;
}

rule sanity(
	env e,
	calldataarg args,
	method f
) filtered {
	f -> !functionsThatRevert(f)
	  && f.selector != sig:setVariableDebtToken(address).selector /* FIXME: This function causes timeout, but should be tested. */
} {
	f(e, args);
	satisfy true;
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

rule initializeCorrectness(
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
	bool initializerBefore = initializing_ghost || isConstructor_ghost || ATOKEN_REVISION() > lastInitializedRevision_ghost;

	initialize(e, initializingPool, treasury, underlyingAsset, incentivesController, aTokenDecimals, aTokenName, aTokenSymbol, params);

	assert initializerBefore;
	assert POOL() == initializingPool;
	assert RESERVE_TREASURY_ADDRESS() == treasury;
	assert UNDERLYING_ASSET_ADDRESS() == underlyingAsset;
	assert getIncentivesController() == incentivesController;
	assert decimals() == aTokenDecimals;
}
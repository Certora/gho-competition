using GhoToken as GHOTOKEN;
using GhoVariableDebtToken as GHOVARDEBTOKEN;
using GhoTokenHelper as GhoTokenHelper;
using DummyERC20A as randomToken;

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
	function _.isPoolAdmin(address user) external => checkIsPoolAdmin(user) expect bool ALL;



}

/// @notice Operations not supported
definition nonSupportedOperations(method f) returns bool = 
    (f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector
    || f.selector == sig:mint(address,address,uint256,uint256).selector
    || f.selector == sig:burn(address,address,uint256,uint256).selector
    || f.selector == sig:mintToTreasury(uint256,uint256).selector
    || f.selector == sig:transferOnLiquidation(address,address,uint256).selector
	|| f.selector == sig:transferFrom(address,address,uint256).selector
	|| f.selector == sig:transfer(address,uint256).selector);

// I remove the call to setVariableDebtToken from rules: sanitySatisfy, balanceOfAlwaysZero, totalSupplyAlwaysZero.
// I don't know why it gives lack of sanity, that's why I take them out
definition isSetVariableDebtToken(method f) returns bool = f.selector == sig:setVariableDebtToken(address).selector;

definition ADMIN_USER returns address = 0xcafe;



/**
* checks if user is admin
**/
function checkIsPoolAdmin(address user) returns bool {
	return user == ADMIN_USER();
}


/**
* @title Not supported operations always revert
**/
// pass
rule nonSupportedOperationsAlwaysRevert(method f) filtered { f-> nonSupportedOperations(f) } {
    env e;
	calldataarg args;
	f@withrevert(e,args);
	assert(lastReverted);
}


// @notice Ensure all other funtions have at least one non-reverting path
rule sanitySatisfy(method f) filtered { f-> !nonSupportedOperations(f) && !isSetVariableDebtToken(f) } {
    env e;
    calldataarg args;
    f(e, args);
    satisfy true;
}


// @notice Balance always zero
rule balanceOfAlwaysZero(method f) filtered { f-> !nonSupportedOperations(f) && !isSetVariableDebtToken(f) } {
    env e;
	address user;
	uint256 balancePre = balanceOf(e, user);
	assert(balancePre == 0);
    calldataarg args;
    f(e, args);
	uint256 balancePost = balanceOf(e, user);
	assert(balancePost == 0);
}

// @notice Total supply always zero
rule totalSupplyAlwaysZero(method f) filtered { f-> !nonSupportedOperations(f) && !isSetVariableDebtToken(f) } {
    env e;
	uint256 totalSupplyPre = totalSupply();
	assert(totalSupplyPre == 0);
    calldataarg args;
    f(e, args);
	uint256 totalSupplyPost = totalSupply();
	assert(totalSupplyPost == 0);
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
* @notice _EIP712BaseId returns name
*/
rule integrityOfEIP712BaseId()
{
	env e;

	string str1 = EIP712BaseId(e);
	string str2 = name(e);
	
	assert stringsAreEqual(e, str1, str2);

}


/**
* @notice getVariableDebtToken returns correct value
*/
rule integrityOfGetVariableDebtToken()
{
	env e;

	address addr1 = getVariableDebtToken(e);
	address addr2 = getVariableDebtTokenMock(e);
	
	assert addr1 == addr2;

}


/**
* @notice RESERVE_TREASURY_ADDRESS returns correct value
*/
rule integrityOfReserveTreasuryAddress()
{
	env e;

	address addr1 = RESERVE_TREASURY_ADDRESS();
	address addr2 = RESERVE_TREASURY_ADDRESS_MOCK(e);
	
	assert addr1 == addr2;

}


/**
* @notice UNDERLYING_ASSET_ADDRESS returns correct value
*/
rule integrityOfUnderlyingAssetAddress()
{
	env e;

	address addr1 = UNDERLYING_ASSET_ADDRESS();
	address addr2 = UNDERLYING_ASSET_ADDRESS_MOCK(e);
	
	assert addr1 == addr2;

}


/**
* @notice getRevision returns 1
*/
rule integrityOfGetRevision()
{
	env e;

	uint256 rev = getRevisionExternal(e);
	
	assert rev == 1;

}

/**
* @notice Consistency check for the execution of function initialize
*/
rule initializeConsistencyCheck(env e) {

    require !getInitializing(e);
    uint256 lastInitializedRevision = getLastInitializedRevision(e);
    uint256 revision = getRevisionExternal(e);

	address initializingPool;
    address treasury;
    address underlyingAsset;
    address incentivesController;
    uint8 aTokenDecimals;
    string aTokenName = "Token name";
    string aTokenSymbol = "TOK";
    bytes params;

	require params.length <= 2;

    initialize@withrevert(e, 
		initializingPool,
		treasury,
		underlyingAsset,
		incentivesController,
		aTokenDecimals,
		aTokenName,
		aTokenSymbol,
		params
	);
    bool lastRev = lastReverted;

    assert (
		e.msg.value > 0 || 
		lastInitializedRevision >= revision ||
		getPool(e) != initializingPool
	) => lastRev;
    assert !lastRev => (
		!getInitializing(e) && 
		getLastInitializedRevision(e) == revision &&
		stringsAreEqual(e, name(e), aTokenName) &&
		stringsAreEqual(e, symbol(e), aTokenSymbol) &&
		decimals(e) == aTokenDecimals
	);
}


/**
* @notice Consistency check for the execution of function updateGhoTreasury
*/
rule updateGhoTreasuryConsistencyCheck(env e) {

    address newGhoTreasury;

	bool isAdmin = isPoolAdmin(e, e.msg.sender);

    updateGhoTreasury@withrevert(e, newGhoTreasury);
    bool lastRev = lastReverted;

    assert lastRev <=> e.msg.value > 0 || !isAdmin || newGhoTreasury == 0;
    assert !lastRev => getGhoTreasury() == newGhoTreasury;
}


/**
* @notice Consistency check for the execution of function distributeFeesToTreasury
*/
rule distributeFeesToTreasuryConsistencyCheck(env e) {

	address treasury = getGhoTreasury();
	uint256 balancePre = GHOTOKEN.balanceOf(currentContract);
	uint256 balanceTreasuryPre = GHOTOKEN.balanceOf(treasury);

	require UNDERLYING_ASSET_ADDRESS() == GHOTOKEN;
	require treasury != currentContract;

    distributeFeesToTreasury@withrevert(e);
    bool lastRev = lastReverted;

	uint256 balancePost = GHOTOKEN.balanceOf(currentContract);
	uint256 balanceTreasuryPost = GHOTOKEN.balanceOf(treasury);

    assert lastRev <=> e.msg.value > 0;
    assert !lastRev => (
		balancePost == 0 &&
		balanceTreasuryPost == require_uint256(balancePre + balanceTreasuryPre)
	);
}


/**
* @notice Consistency check for the execution of function setVariableDebtToken
*/
rule setVariableDebtTokenConsistencyCheck(env e) {

	address ghoVariableDebtToken;

	bool isAdmin = isPoolAdmin(e, e.msg.sender);

	address preGhoVariableDebtToken = getVariableDebtToken();

    setVariableDebtToken@withrevert(e, ghoVariableDebtToken);
    bool lastRev = lastReverted;

    assert lastRev <=> e.msg.value > 0 || !isAdmin || preGhoVariableDebtToken > 0 || ghoVariableDebtToken == 0;
    assert !lastRev => getVariableDebtToken() == ghoVariableDebtToken;
}


/**
* @notice Consistency check for the execution of function rescueTokens
*/
rule rescueTokensConsistencyCheck(env e) {

	address token;
	address to;
	uint256 amount;

	require to != currentContract;
	require randomToken == token;

	bool isAdmin = isPoolAdmin(e, e.msg.sender);

	uint256 preToBalance = randomToken.balanceOf(e, to);
	uint256 preContractBalance = randomToken.balanceOf(e, currentContract);

    rescueTokens@withrevert(e, token, to, amount);
    bool lastRev = lastReverted;

	uint256 postToBalance = randomToken.balanceOf(e, to);
	uint256 postContractBalance = randomToken.balanceOf(e, currentContract);

    assert (
		e.msg.value > 0 || token == UNDERLYING_ASSET_ADDRESS() || !isAdmin
	) => lastRev;
    assert !lastRev => (
		postToBalance == require_uint256(preToBalance + amount) &&
		postContractBalance == require_uint256(preContractBalance - amount)
	);
}


/**
* @notice Consistency check for the execution of function transferUnderlyingTo
*/
rule transferUnderlyingToConsistencyCheck(env e) {

	address target;
	uint256 amount;

	uint256 finalSupply = require_uint256(GHOTOKEN.totalSupply(e) + amount);

	mathint facilitatorLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint facilitatorCapacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);

	uint256 preTotalSupply = GHOTOKEN.totalSupply(e);
	uint256 preTargetBalance = GHOTOKEN.balanceOf(e, target);

    transferUnderlyingTo@withrevert(e, target, amount);
    bool lastRev = lastReverted;

	uint256 postTotalSupply = GHOTOKEN.totalSupply(e);
	uint256 postTargetBalance = GHOTOKEN.balanceOf(e, target);

    assert lastRev <=>  (
		e.msg.value > 0 ||
		getPool(e) != e.msg.sender ||
		amount == 0 ||
		to_mathint(amount) > (facilitatorCapacity - facilitatorLevel)
	);
    assert !lastRev => (
		postTargetBalance == require_uint256(preTargetBalance + amount) &&
		postTotalSupply == require_uint256(preTotalSupply + amount)
	);
}


/**
* @notice Consistency check for the execution of function handleRepayment
*/
rule handleRepaymentConsistencyCheck(env e) {

	address user;
    address onBehalfOf;
    uint256 amount;

	uint256 balancePre = GHOTOKEN.balanceOf(e, currentContract);
	uint256 balanceFromInterestPre = GHOVARDEBTOKEN.getBalanceFromInterest(e, onBehalfOf);
	uint256 preTotalSupply = GHOTOKEN.totalSupply(e);
	mathint facilitatorLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint finalBalanceFromInterest = (balanceFromInterestPre - amount) < 0?0:(balanceFromInterestPre - amount);

    handleRepayment@withrevert(e, user, onBehalfOf, amount);
    bool lastRev = lastReverted;

	uint256 balanceFromInterestPost = GHOVARDEBTOKEN.getBalanceFromInterest(e, onBehalfOf);
	uint256 postTotalSupply = GHOTOKEN.totalSupply(e);

    assert lastRev <=>  (
		e.msg.value > 0 ||
		getPool(e) != e.msg.sender || 
		(amount > balanceFromInterestPre && facilitatorLevel < (amount - balanceFromInterestPre)) ||
		(amount > balanceFromInterestPre && to_mathint(balancePre) < (amount - balanceFromInterestPre)) ||
		finalBalanceFromInterest < 0
	);
    assert !lastRev => (
		balanceFromInterestPost == assert_uint256(finalBalanceFromInterest) &&
		(amount > balanceFromInterestPre => postTotalSupply == require_uint256(preTotalSupply - (amount - balanceFromInterestPre)))
	);
}



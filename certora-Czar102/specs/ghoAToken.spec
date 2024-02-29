using GhoToken as GHOTOKEN;
using GhoTokenHelper as GhoTokenHelper;
using GhoVariableDebtToken as ghoVDT;
using GhoATokenHarness as GhoATokenHarness;

methods{
	// erc20 methods
    function _.name() external                            ;
    function _.symbol() external                          ;
    function _.decimals() external                            => DISPATCHER(true);
    function _.totalSupply() external                         => DISPATCHER(true);
    function _.balanceOf(address) external                    => DISPATCHER(true);
    function _.allowance(address,address) external            => DISPATCHER(true);
    function _.approve(address,uint256) external              => DISPATCHER(true);
    function _.transfer(address,uint256) external             => DISPATCHER(true);
    function _.transferFrom(address,address,uint256) external => DISPATCHER(true);

	function totalSupply() external returns (uint256) envfree;
	function RESERVE_TREASURY_ADDRESS() external returns (address) envfree;
	function POOL() external returns (address) envfree;
	function UNDERLYING_ASSET_ADDRESS() external returns (address) envfree;
	function DOMAIN_SEPARATOR() external returns (bytes32) envfree;
	function getIncentivesController() external returns (address) envfree;
	function transferUnderlyingTo(address,uint256) external;
	function handleRepayment(address,address,uint256) external; 
	function distributeFeesToTreasury() external envfree ;
	function rescueTokens(address,address,uint256) external; 
	function setVariableDebtToken(address)  external;
	function getVariableDebtToken() external returns (address) envfree;
	function updateGhoTreasury(address) external ;
	function getGhoTreasury() external returns (address) envfree;
	function scaledBalanceOf(address) external returns (uint256) envfree;

	function name() external returns (string) envfree;
	function symbol() external returns (string) envfree;
	function decimals() external returns (uint8) envfree;

	function initialize(address,address,address,address,uint8,string,string,bytes) external;
	/*******************
    *   GhoToken.sol   *
    ********************/
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns (uint256) envfree;
	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns (uint256) envfree;
	function GhoTokenHelper.nullAddress() external returns (address) envfree;
	function GHOTOKEN.balanceOf(address) external returns (uint256) envfree;
	function GHOTOKEN.totalSupply() external returns (uint256) envfree;

	/************************************
    *   GhoTokenVariableDebtToken.sol   *
    *************************************/
	function _.getBalanceFromInterest(address user) external  => DISPATCHER(true);
	function _.decreaseBalanceFromInterest(address user, uint256 amount) external => DISPATCHER(true);

	function ghoVDT.getBalanceFromInterest(address user) external returns uint envfree;
	function ghoVDT.decreaseBalanceFromInterest(address user, uint256 amount) external;

  	/*******************
    *     Pool.sol     *
    ********************/
    function _.getReserveNormalizedIncome(address) external => CONSTANT;


  	/***********************************
    *    PoolAddressesProvider.sol     *
    ************************************/
	function _.getACLManager() external => GhoTokenHelper expect address ALL;

	// pool
	function _.ADDRESSES_PROVIDER() external => NONDET;


	/************************
    *    ACLManager.sol     *
    *************************/
	function _.isPoolAdmin(address a) external => isPoolAdminGhost[a] expect bool ALL;

	function GhoTokenHelper.isPoolAdmin(address a) external returns bool envfree => isPoolAdminGhost[a];
	function GhoTokenHelper.isPoolAdminSummarized(address a) external returns bool envfree;
	function GhoTokenHelper.areStringsSame(string,string) external returns (bool) envfree;
	function GhoTokenHelper.compare(string,string) external returns (bool) envfree;
	function GhoTokenHelper.balanceOf(address token, address user) external returns (uint);
}

ghost bool initializingGhost {
	init_state axiom !initializingGhost;
}

hook Sload bool value initializing STORAGE {
	require initializingGhost == value;
}

hook Sstore initializing bool value (bool old_value) STORAGE {
	initializingGhost = value;
}

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


ghost mapping (address => bool) isPoolAdminGhost;

ghost address underlyingAsset {
	init_state axiom underlyingAsset == 0;
}

hook Sload address asset _underlyingAsset STORAGE {
	require underlyingAsset == asset;
}

hook Sstore _underlyingAsset address asset (address old_asset) STORAGE {
	underlyingAsset = asset;
}

ghost address ghoTreasury {
	init_state axiom ghoTreasury == 0;
}

hook Sload address treasury _ghoTreasury STORAGE {
	require ghoTreasury == treasury;
}

hook Sstore _ghoTreasury address treasury (address old_treasury) STORAGE {
	ghoTreasury = treasury;
}

ghost address vdToken {
	init_state axiom vdToken == 0;
}

hook Sload address token _ghoVariableDebtToken STORAGE {
	require vdToken == token;
}

hook Sstore _ghoVariableDebtToken address token (address old_token) STORAGE {
	vdToken = token;
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

/**
* @title Proves that the revision never decreases
**/
rule revisionIntegrity() {
	method f; calldataarg arg; env e;
	require lastInitializedRevisionGhost == 1;

	f(e, arg);

	assert lastInitializedRevisionGhost == 1;
}

/**
* @title Makes sure that the revision is at most 1
**/
invariant revisionMax1()
	lastInitializedRevisionGhost <= 1;

/**
* @title Makes sure that the variable debt token read function operates properly
**/
invariant integrityOfRead()
	getVariableDebtToken() == vdToken;

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
	
	address pool;
	address treasury;
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
	
	initialize@withrevert(e, pool, treasury, underlying, ic, decimals, name, symbol, params);
	bool reverted = lastReverted;

	assert (reverted => (
		pool != POOL() ||
		prevRevision == 1 ||
		e.msg.value != 0
	)) && ((
		pool != POOL() ||
		prevRevision == 1 ||
		e.msg.value != 0
	) => reverted);

	assert !reverted => (
		treasury == RESERVE_TREASURY_ADDRESS() &&
		underlying == UNDERLYING_ASSET_ADDRESS() &&
		ic == getIncentivesController() &&
		decimals == decimals() &&
		GhoTokenHelper.areStringsSame(symbol, symbol()) &&
		GhoTokenHelper.areStringsSame(name, name()) &&
		DOMAIN_SEPARATOR() != to_bytes32(0)
	);
}

/**
* @title ensures the state change and revert reasons of the transferUnderlyingTo() function are as intended
**/
rule transferUnderlyingToIntegrity() {
	env e;
	address to;
	uint amount;
	bool isPool = (e.msg.sender == POOL());
	uint level = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	uint capacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);

	uint balanceOfBefore = GHOTOKEN.balanceOf(to);
	require balanceOfBefore + amount <= max_uint256;

	require (GHOTOKEN.totalSupply() + amount) <= max_uint256;

	transferUnderlyingTo@withrevert(e, to, amount);
	bool reverted = lastReverted;

	assert reverted <=> (
		amount + level > to_mathint(capacity) ||
		!isPool ||
		amount == 0 ||
		e.msg.value != 0
	);

	assert !reverted => (
		to_mathint(GHOTOKEN.balanceOf(to)) == balanceOfBefore + amount
	);
}

/**
* @title ensures the state change and revert reasons of the distributeFeesToTreasury() function are as intended
**/
rule distributeFeesToTreasuryIntegrity() {
	env e;
	uint balanceOfTreasuryBefore = GHOTOKEN.balanceOf(ghoTreasury);
	uint balanceOfContractBefore = GHOTOKEN.balanceOf(currentContract);
	require balanceOfTreasuryBefore + balanceOfContractBefore <= max_uint256;

	distributeFeesToTreasury@withrevert();
	bool reverted = lastReverted;

	assert !reverted;

	assert !reverted => (
		GHOTOKEN.balanceOf(currentContract) == 0 &&
		to_mathint(GHOTOKEN.balanceOf(ghoTreasury)) == balanceOfTreasuryBefore + balanceOfContractBefore ||
		currentContract == ghoTreasury
	);
}

/**
* @title ensures the state change and revert reasons of the rescueTokens() function are as intended
**/
rule rescueTokensIntegrity() {
	env e;

	env any;
	require any.msg.value == 0;
	address to;
	address token;
	uint amount;

	uint balanceOfBefore = GhoTokenHelper.balanceOf(any, token, currentContract);
	uint balanceOfToBefore = GhoTokenHelper.balanceOf(any, token, to);

	// let's see if this is required
	// require token != currentContract;
	require balanceOfBefore + balanceOfToBefore <= max_uint256;
	require token != currentContract;
	require token != ghoVDT;

	rescueTokens@withrevert(e, token, to, amount);
	bool reverted = lastReverted;

	assert reverted <=> (
		token == underlyingAsset ||
		!GhoTokenHelper.isPoolAdminSummarized(e.msg.sender) ||
		balanceOfBefore < amount ||
		e.msg.value != 0
	);

	assert !reverted => (
		(
			(to_mathint(GhoTokenHelper.balanceOf(any, token, to)) == amount + balanceOfToBefore &&
			to_mathint(GhoTokenHelper.balanceOf(any, token, currentContract)) == balanceOfBefore - amount) ||
			(to == currentContract &&
			GhoTokenHelper.balanceOf(any, token, currentContract) == balanceOfBefore)
		)
	);
}

/**
* @title ensures the state change and revert reasons of the setVariableDebtToken() function are as intended
**/
rule setVariableDebtTokenIntegrity() {
	env e;

	address newVdToken;
	address prevVdToken = vdToken;

	setVariableDebtToken@withrevert(e, newVdToken);
	bool reverted = lastReverted;

	assert reverted <=> (
		prevVdToken != GhoTokenHelper.nullAddress() ||
		newVdToken == GhoTokenHelper.nullAddress() ||
		!GhoTokenHelper.isPoolAdminSummarized(e.msg.sender) ||
		e.msg.value != 0
	);

	assert !reverted => (
		vdToken == newVdToken
	);
}

/**
* @title ensures the state change and revert reasons of the updateGhoTreasury() function are as intended
**/
rule updateGhoTreasuryIntegrity() {
	env e;
	address newTreasury;

	updateGhoTreasury@withrevert(e, newTreasury);
	bool reverted = lastReverted;

	assert reverted <=> (
		newTreasury == GhoTokenHelper.nullAddress() ||
		!GhoTokenHelper.isPoolAdminSummarized(e.msg.sender) ||
		e.msg.value != 0
	);

	assert !reverted => (
		getGhoTreasury() == newTreasury
	);
}

/**
* @title ensures the state change and revert reasons of the handleRepayment() function are as intended
**/
rule handleRepaymentIntegrity() {
	env e;
	bool isPool = (e.msg.sender == POOL());
	address user;
	address for;
	uint amount;

	uint initBalanceFromInterest = ghoVDT.getBalanceFromInterest(for);
	uint initBalanceOfAToken = GHOTOKEN.balanceOf(currentContract);
	uint lavelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	handleRepayment@withrevert(e, user, for, amount);
	bool reverted = lastReverted;

	uint burnAmount = 0;
	if (amount > initBalanceFromInterest) {
		burnAmount = assert_uint256(amount - initBalanceFromInterest);
	}
	uint interestDecrease = assert_uint256(amount - burnAmount);

	assert reverted <=> (
		lavelBefore < burnAmount ||
		initBalanceOfAToken < burnAmount ||
		!isPool ||
		e.msg.value != 0
	);

	assert !reverted => (
		ghoVDT.getBalanceFromInterest(for) + interestDecrease == to_mathint(initBalanceFromInterest) &&
		GHOTOKEN.balanceOf(currentContract) + burnAmount == to_mathint(initBalanceOfAToken)
	);
}

function mustRevert(method f) returns bool {
	return f.selector == sig:mint(address,address,uint,uint).selector ||
		f.selector == sig:burn(address,address,uint,uint).selector ||
		f.selector == sig:mintToTreasury(uint,uint).selector ||
		f.selector == sig:transferOnLiquidation(address,address,uint).selector ||
		f.selector == sig:permit(address,address,uint,uint, uint8,bytes32,bytes32).selector ||
		f.selector == sig:transfer(address,uint256).selector ||
		f.selector == sig:transferFrom(address,address,uint256).selector;
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

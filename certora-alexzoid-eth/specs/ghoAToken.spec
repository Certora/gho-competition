import "./methods/GhoTokenHelperMethods.spec";
import "./methods/ScaledBalanceTokenBaseMethods.spec";
import "./methods/EIP712BaseMethods.spec";
import "./helpers/VersionedInitializable.spec";
import "./helpers/EIP712Base.spec";
import "./helpers/IncentivizedERC20.spec";

using GhoTokenHarness as _GhoTokenHarness;
using GhoVariableDebtTokenHarness as _GhoVariableDebtTokenHarness;
using DummyERC20A as _DummyERC20A;

///////////////// METHODS //////////////////////

methods{

    //
    // Current contract
    //

    // GhoATokenHarness
    function getRevisionHarness() external returns (uint256) envfree;
    function getPoolAddress() external returns (address) envfree;
    function calculateDomainSeparator() external returns (bytes32);
    function isPoolAdmin(address account) external returns (bool);
    function setName1() external envfree;
    function setName2() external envfree;

    // GhoAToken
    function ATOKEN_REVISION() external returns (uint256) envfree;
    function initialize(address initializingPool, address treasury, address underlyingAsset, 
        address incentivesController, uint8 aTokenDecimals, string memory aTokenName, 
        string memory aTokenSymbol, bytes calldata params) external;
    function mint(address caller, address onBehalfOf, uint256 amount, uint256 index) external returns (bool); // Always reverts
    function burn(address from, address receiverOfUnderlying, uint256 amount, uint256 index) external; // Always reverts
    function mintToTreasury(uint256 amount, uint256 index) external; // Always reverts
    function transferOnLiquidation(address from, address to, uint256 value) external; // Always reverts
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function RESERVE_TREASURY_ADDRESS() external returns (address) envfree;
    function UNDERLYING_ASSET_ADDRESS() external returns (address) envfree;
    function transferUnderlyingTo(address target, uint256 amount) external;
    function handleRepayment(address user, address onBehalfOf, uint256 amount) external; 
    function distributeFeesToTreasury() external;
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, 
        bytes32 r, bytes32 s) external; // Always reverts
    function _transfer(address from, address to, uint128 amount) internal;
    function DOMAIN_SEPARATOR() internal returns (bytes32);
    function _EIP712BaseId() internal returns (string memory);
    function rescueTokens(address token, address to, uint256 amount) external;
    function setVariableDebtToken(address ghoVariableDebtToken) external;
    function getVariableDebtToken() external returns (address) envfree;
    function updateGhoTreasury(address newGhoTreasury) external;
    function getGhoTreasury() external returns (address) envfree;

    //
    // External calls
    //

    // _DummyERC20A, GhoToken
    function _.balanceOf(address) external => DISPATCHER(true);

    // GhoToken
    function _.transfer(address to, uint256 amount) external => DISPATCHER(true);
    function _.mint(address account, uint256 amount) external => DISPATCHER(true);
    function _.burn(uint256 amount) external => DISPATCHER(true);
    function _.totalSupply() external => DISPATCHER(true);

    // GhoTokenVariableDebtToken
    function _.getBalanceFromInterest(address user) external => DISPATCHER(true);
    function _.decreaseBalanceFromInterest(address user, uint256 amount) external => DISPATCHER(true);

    // IERC20(token)
    function _.safeTransfer(address, uint256) external => DISPATCHER(true);

    // Pool
    function _.ADDRESSES_PROVIDER() external => CONSTANT;

    // PoolAddressesProvider
    function _.getACLManager() external => CONSTANT;

    // ACLManager
    function _.isPoolAdmin(address) external => CONSTANT;
}

///////////////// DEFINITIONS /////////////////////

definition VIEW_FUNCTIONS(method f) returns bool = f.isView || f.isPure;

definition ALWAYS_REVERT_FUNCTIONS(method f) returns bool = 
    f.selector == sig:mint(address, address, uint256, uint256).selector
    || f.selector == sig:burn(address, address, uint256, uint256).selector
    || f.selector == sig:mintToTreasury(uint256, uint256).selector
    || f.selector == sig:transferOnLiquidation(address, address, uint256).selector
    || f.selector == sig:transfer(address, uint256).selector
    || f.selector == sig:transferFrom(address, address, uint256).selector
    || f.selector == sig:permit(address, address, uint256, uint256, uint8, bytes32, bytes32).selector
    ;

definition INITIALIZE_FUNCTION(method f) returns bool = 
    f.selector == sig:initialize(address, address, address, address, uint8, string, string, bytes).selector;

definition HANDLE_REPAYMENT_FUNCTION(method f) returns bool = 
    f.selector == sig:handleRepayment(address, address, uint256).selector;

definition DISTRIBUTE_FEES_TO_TREASUTY_FUNCTION(method f) returns bool = 
    f.selector == sig:distributeFeesToTreasury().selector;

definition BURN_USE_FUNCTION(method f) returns bool = 
    f.selector == sig:transferUnderlyingTo(address, uint256).selector;

definition MINT_USE_FUNCTION(method f) returns bool = 
    f.selector == sig:handleRepayment(address, address, uint256).selector;

definition BURN_MINT_USE_FUNCTIONS(method f) returns bool = 
    BURN_USE_FUNCTION(f) || MINT_USE_FUNCTION(f);


////////////////// FUNCTIONS //////////////////////

function setUp() {
    require(_GhoTokenHarness == ghostUnderlyingAsset);
    require(_GhoVariableDebtTokenHarness == ghostGhoVariableDebtToken);

    require(ghostGhoTreasury != _GhoTokenHarness);
    require(ghostGhoTreasury != _GhoVariableDebtTokenHarness);
    require(ghostGhoTreasury != currentContract);
}

///////////////// GHOSTS & HOOKS //////////////////

//
// Ghost copy of `_treasury`
//

ghost address ghostTreasury {
    init_state axiom ghostTreasury == 0;
}

hook Sload address val currentContract._treasury STORAGE {
    require(ghostTreasury == val);
}

hook Sstore currentContract._treasury address val STORAGE {
    ghostTreasury = val;
}

//
// Ghost copy of `_underlyingAsset`
//

ghost address ghostUnderlyingAsset {
    init_state axiom ghostUnderlyingAsset == 0;
}

hook Sload address val currentContract._underlyingAsset STORAGE {
    require(ghostUnderlyingAsset == val);
}

hook Sstore currentContract._underlyingAsset address val STORAGE {
    ghostUnderlyingAsset = val;
}

//
// Ghost copy of `_ghoVariableDebtToken`
//

ghost bool ghostGhoVariableDebtTokenWritten;

ghost address ghostGhoVariableDebtToken {
    init_state axiom ghostGhoVariableDebtToken == 0;
}

hook Sload address val currentContract._ghoVariableDebtToken STORAGE {
    require(ghostGhoVariableDebtToken == val);
}

hook Sstore currentContract._ghoVariableDebtToken address val STORAGE {
    ghostGhoVariableDebtToken = val;
    ghostGhoVariableDebtTokenWritten = true;
}

//
// Ghost copy of `_ghoTreasury`
//

ghost bool ghostGhoTreasuryWritten;

ghost address ghostGhoTreasury {
    init_state axiom ghostGhoTreasury == 0;
}

hook Sload address val currentContract._ghoTreasury STORAGE {
    require(ghostGhoTreasury == val);
}

hook Sstore currentContract._ghoTreasury address val STORAGE {
    ghostGhoTreasury = val;
    ghostGhoTreasuryWritten = true;
}

//
// Check if GHO token was called
//

ghost bool ghoTokenCalled;

hook CALL(uint g, address addr, uint value, uint argsOffset, uint argsLength, uint retOffset, uint retLength) uint rc {
    ghoTokenCalled = addr == ghostUnderlyingAsset ? true : ghoTokenCalled;
}

///////////////// PROPERTIES //////////////////////

// Proves that ghoAToken::mint always reverts
rule noMint(env e, calldataarg args) {
    mint@withrevert(e, args);
    assert(lastReverted);
}

// Proves that ghoAToken::burn always reverts
rule noBurn(env e, calldataarg args) {
    burn@withrevert(e, args);
    assert(lastReverted);
}

// Proves that ghoAToken::transfer always reverts
rule noTransfer(env e, calldataarg args) {
    transfer@withrevert(e, args);
    assert(lastReverted);
}

// Proves that calling ghoAToken::transferUnderlyingTo will revert if the amount exceeds the excess 
//  capacity. A user can’t borrow more than the facilitator’s remaining capacity.
rule transferUnderlyingToCantExceedCapacity() {

    // Added
    setUp();

    address target;
    uint256 amount;
    env e;
    mathint facilitatorLevel = _GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
    mathint facilitatorCapacity = _GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);
    
    transferUnderlyingTo@withrevert(e, target, amount);
    
    assert(to_mathint(amount) > (facilitatorCapacity - facilitatorLevel) => lastReverted);
}

// Proves that the total supply of GhoAToken is always zero
rule totalSupplyAlwaysZero() {
    assert(totalSupply() == 0);
} 

// Proves that any user's balance of GhoAToken is always zero
rule userBalanceAlwaysZero(address user) {
    assert(balanceOf(user) == 0);
}

// BucketLevel decreases after transferUnderlyingTo() followed by handleRepayment(). repayment 
//  funds are, partially or fully, transferred to the treasury
rule integrityTransferUnderlyingToWithHandleRepayment() {

    // Added
    setUp();

    env e;
    calldataarg arg;
    uint256 amount;
    address target;
    address user;
    address onBehalfOf;

    uint256 levelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
    transferUnderlyingTo(e, target, amount);
    handleRepayment(e, user, onBehalfOf, amount);
    uint256 levelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

    assert(levelBefore <= levelAfter);
}

///////////////// ADDED PROPERTIES //////////////////////

// [2] Initialize could be executed once
use rule initializeCouldBeExecutedOnce;

// [3] Could be initialized with specific pool address only
rule initializedWithSpecificPoolAddressOnly(
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
    
    initialize@withrevert(e, initializingPool, treasury, underlyingAsset, incentivesController, 
        aTokenDecimals, aTokenName, aTokenSymbol, params);
    bool reverted = lastReverted;

    assert(initializingPool != getPoolAddress() => reverted);
}

// [4,27] Initialize set initial params correctly
rule initializeSetInitialParamsCorrectly(
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
    require(aTokenName.length < 16);
    require(aTokenSymbol.length < 16);

    initialize(e, initializingPool, treasury, underlyingAsset, incentivesController, 
        aTokenDecimals, aTokenName, aTokenSymbol, params);

    string n = name(e);
    string s = symbol();
    uint256 ni;
    require(ni < n.length && ni < aTokenName.length);
    uint256 si;
    require(si < s.length && si < aTokenSymbol.length);

    assert(
        treasury == RESERVE_TREASURY_ADDRESS()
        && underlyingAsset == UNDERLYING_ASSET_ADDRESS()
        && incentivesController == getIncentivesController()
        && aTokenDecimals == decimals()
        && aTokenName.length == n.length
        && aTokenSymbol.length == s.length
        && DOMAIN_SEPARATOR(e) == calculateDomainSeparator(e)
    );
}

// [5] Specific functions always reverts
rule specificFunctionsAlwaysRevert(env e, method f, calldataarg args) 
    filtered { f -> ALWAYS_REVERT_FUNCTIONS(f) } {

    f@withrevert(e, args);
    
    assert(lastReverted);
}

// Viewers integrity
rule viewersIntegrity(env e) {

    calculateDomainSeparator(e);

    assert(
        getRevisionHarness() == ATOKEN_REVISION()
        && RESERVE_TREASURY_ADDRESS() == ghostTreasury
        && UNDERLYING_ASSET_ADDRESS() == ghostUnderlyingAsset
        && getVariableDebtToken() == ghostGhoVariableDebtToken
        && getGhoTreasury() == ghostGhoTreasury
        // && DOMAIN_SEPARATOR(e) == ghostDomainSeparator // Issue with hooking Sstore _domainSeparator
        && decimals() == ghostDecimals
        && getIncentivesController() == ghostIncentivesController
        // TODO: scaledBalanceOf, getScaledUserBalanceAndSupply, scaledTotalSupply, getPreviousIndex
    );
}

// [7] Only Pool admin could set Treasury, VariableDebtToken, IncentivesController (expect in `initialize()`)
rule onlyPoolAdminCouldUpdateCriticalAddresses(env e, method f, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {

    address ghoTreasuryBefore = ghostGhoTreasury; 
    address ghoVariableDebtTokenBefore = ghostGhoVariableDebtToken;
    address incentivesControllerBefore = ghostIncentivesController;

    f@withrevert(e, args);
    bool reverted = lastReverted;

    bool changed = ghoTreasuryBefore != ghostGhoTreasury
        || ghoVariableDebtTokenBefore != ghostGhoVariableDebtToken
        || incentivesControllerBefore != ghostIncentivesController;

    assert(!reverted && changed => isPoolAdmin(e, e.msg.sender));
}

// [8] VariableDebtToken could be set once
rule variableDebtTokenSetOnlyOnce(env e, method f, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {

    require(ghostGhoVariableDebtToken != 0);
    address before = ghostGhoVariableDebtToken;

    f@withrevert(e, args);

    assert(!lastReverted => before == ghostGhoVariableDebtToken);
}

// [6,9] System variables (ghoTreasury, ghoVariableDebtToken) could not be set to zero (expect in `initialize()`)
rule systemVariablesNotSetToZero(env e, method f, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {

    require(ghostGhoTreasuryWritten == false);
    require(ghostGhoVariableDebtTokenWritten == false);

    f@withrevert(e, args);
    bool reverted = lastReverted;

    assert(!reverted && ghostGhoTreasuryWritten => ghostGhoTreasury != 0);
    assert(!reverted && ghostGhoVariableDebtTokenWritten => ghostGhoVariableDebtToken != 0);
}

// [28] GhoTreasury could be modified
rule possibilityGhoTreasuryModify(env e, calldataarg args) {
    
    address before = ghostGhoTreasury;

    updateGhoTreasury(e, args);

    address after = ghostGhoTreasury;

    satisfy(before != after && after != 0);
}

// [29] GhoVariableDebtToken could be modified
rule possibilityGhoVariableDebtTokenModify(env e, calldataarg args) {
    
    address before = ghostGhoVariableDebtToken;

    setVariableDebtToken(e, args);

    address after = ghostGhoVariableDebtToken;

    satisfy(before != after && after != 0);
}

// [10] Stuck tokens could be rescued only by pool admin
rule onlyPoolAdminCouldTransferOutTokens(env e, method f, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) } {

    setUp();

    uint256 balanceBefore = _DummyERC20A.balanceOf(e, currentContract);
    require(balanceBefore != 0);

    f@withrevert(e, args);
    bool reverted = lastReverted;

    uint256 balanceAfter = _DummyERC20A.balanceOf(e, currentContract);

    assert(!reverted && balanceBefore > balanceAfter => isPoolAdmin(e, e.msg.sender));
}

// [11] Possibility of rescue stuck tokens 
rule possibilityOfRescueStuckToken(env e, address token, address to, uint256 amount) {

    setUp();

    require(token == _DummyERC20A);
    require(amount != 0);

    uint256 currentBalanceBefore = _DummyERC20A.balanceOf(e, currentContract);
    require(currentBalanceBefore != 0);

    uint256 toBalanceBefore = _DummyERC20A.balanceOf(e, to);
    require(toBalanceBefore == 0);

    rescueTokens(e, token, to, amount);

    uint256 currentBalanceAfter = _DummyERC20A.balanceOf(e, currentContract);
    uint256 toBalanceAfter = _DummyERC20A.balanceOf(e, to);

    satisfy(toBalanceAfter == amount);
}

// [12,14] GHO tokens should be sent to ghoTresaury only. Pool admin could not rug pool GHO tokens 
//  via rescue mechanism. handleRepayment(), which changes balance of current contract via burn() is filtered
rule ghoTokensCouldBeTransferredOutToGhoTresauryOnly(env e, method f, calldataarg args) 
    filtered { f -> !HANDLE_REPAYMENT_FUNCTION(f) && !VIEW_FUNCTIONS(f) } {
    
    setUp();    

    // Current contract has some GHO
    uint256 currentBalanceBefore = _GhoTokenHarness.balanceOf(e, currentContract);
    require(currentBalanceBefore != 0);

    // Balance cannot overflow because the sum of all user sbalances can't exceed the max uint256 value
    uint256 ghoTotalSupply = _GhoTokenHarness.totalSupply(e);
    require(currentBalanceBefore <= ghoTotalSupply);

    // GHO treasury is empty
    uint256 tresauryBalanceBefore = _GhoTokenHarness.balanceOf(e, ghostGhoTreasury);
    require(tresauryBalanceBefore == 0);

    f@withrevert(e, args);
    bool reverted = lastReverted;

    uint256 currentBalanceAfter = _GhoTokenHarness.balanceOf(e, currentContract);
    uint256 transferOutAmount = currentBalanceBefore > currentBalanceAfter  
        ? assert_uint256(currentBalanceBefore - currentBalanceAfter)
        : 0;

    uint256 tresauryBalanceAfter = _GhoTokenHarness.balanceOf(e, ghostGhoTreasury);

    // The whole amount of current contract's balance should be transferred
    assert(!reverted && transferOutAmount != 0 => tresauryBalanceAfter == currentBalanceBefore);
}

// [13,15] Possibility of anyone to withdraw GHO tokens to the GHO Tresaury 
rule possibilityOfTransferOutGhoTokensToTresaury(env e) {

    setUp();    

    // User without any privilege
    address user;
    require(user == e.msg.sender
        && user != currentContract
        && user != ghostGhoTreasury
        && user != _GhoTokenHarness
        && user != getPoolAddress()
        && !isPoolAdmin(e, user)
    );

    // Current contract and treasury have some GHO tokens
    uint256 currentBalanceBefore = _GhoTokenHarness.balanceOf(e, currentContract);
    uint256 userBalance = _GhoTokenHarness.balanceOf(e, user);
    uint256 tresauryBalanceBefore = _GhoTokenHarness.balanceOf(e, ghostGhoTreasury);
    require(currentBalanceBefore != 0 
        && currentBalanceBefore != userBalance 
        && currentBalanceBefore != tresauryBalanceBefore
    );

    // Balance cannot overflow because the sum of all user sbalances can't exceed the max uint256 value
    uint256 ghoTotalSupply = _GhoTokenHarness.totalSupply(e);
    require(require_uint256(currentBalanceBefore + tresauryBalanceBefore) <= ghoTotalSupply);

    distributeFeesToTreasury(e);

    uint256 currentBalanceAfter = _GhoTokenHarness.balanceOf(e, currentContract);
    uint256 transferOutAmount = currentBalanceBefore > currentBalanceAfter  
        ? assert_uint256(currentBalanceBefore - currentBalanceAfter)
        : 0;
    uint256 tresauryBalanceAfter = _GhoTokenHarness.balanceOf(e, ghostGhoTreasury);

    // Any user can withdraw all tokens as a fee to the tresaury
    satisfy(currentBalanceAfter == 0 
        && tresauryBalanceAfter == require_uint256(tresauryBalanceBefore + transferOutAmount)
    );
}

// [16] Domain separator depends on token name
use rule domainSeparatorDepensOnName;

// [17] Only Pool could initialize a communication with GhoToken contract (distributeFeesToTreasury() is an exception)
rule onlyPoolCanInitializeCommunicationWithGHOToken(env e, method f, calldataarg args) 
    filtered { f -> !DISTRIBUTE_FEES_TO_TREASUTY_FUNCTION(f) && !VIEW_FUNCTIONS(f) } {

    require(ghoTokenCalled == false);

    f@withrevert(e, args);
    
    assert(!lastReverted && ghoTokenCalled => e.msg.sender == getPoolAddress());
}

// [18,19] Possibility of change current contract's bucketLevel with mint and burn
rule possibilityOfBurnMintChangeBucketLevel(env e, method f, calldataarg args) 
    filtered { f -> BURN_MINT_USE_FUNCTIONS(f) } {

    require(e.msg.sender == getPoolAddress());

    uint256 bucketLevelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);
    require(bucketLevelBefore != 0);

    uint256 bucketCapacityBefore = _GhoTokenHelper.getFacilitatorBucketCapacity(e, currentContract);
    require(bucketCapacityBefore > bucketLevelBefore);

    f(e, args);
    
    uint256 bucketLevelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);

    satisfy(bucketLevelAfter != bucketLevelBefore);
}

// [20] Only bucketLevel of current contract could be changed
rule noAnotherUserBucketLevelCouldBeChanged(env e, method f, calldataarg args, address anotherUser) 
    filtered { f -> !VIEW_FUNCTIONS(f) } {

    require(anotherUser != currentContract);

    uint256 bucketLevelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e, anotherUser);

    f@withrevert(e, args);
    bool reverted = lastReverted;

    uint256 bucketLevelBeforeAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e, anotherUser);

    assert(!reverted => bucketLevelBefore == bucketLevelBeforeAfter);
}

// [21] Possibility of decrease whole balance of sGHO tokens
rule possibilityDecreaseWholeBalance(env e, address user, address onBehalfOf, uint256 amount) {
    
    setUp();

    uint256 balance = _GhoVariableDebtTokenHarness.getUserAccumulatedDebtInterest(e, onBehalfOf);
    require(balance == amount);

    handleRepayment@withrevert(e, user, onBehalfOf, amount);

    satisfy(!lastReverted);
}

// [1, 22-26] handleRepayment() should burn anything more than balance from interest
rule handleRepaymentBurnAnythingMoreBalanceFromInterest(
    env e, address user, address onBehalfOf, uint256 amount
) {
    
    setUp();

    uint256 bucketLevelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);
    require(bucketLevelBefore != 0);

    uint256 bucketCapacityBefore = _GhoTokenHelper.getFacilitatorBucketCapacity(e, currentContract);
    require(bucketCapacityBefore > bucketLevelBefore);

    uint256 balanceFromInterestBefore = _GhoVariableDebtTokenHarness.getUserAccumulatedDebtInterest(e, onBehalfOf);

    handleRepayment(e, user, onBehalfOf, amount);

    uint256 bucketLevelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);
    uint256 balanceFromInterestAfter = _GhoVariableDebtTokenHarness.getUserAccumulatedDebtInterest(e, onBehalfOf);

    assert(amount > balanceFromInterestBefore 
        ? assert_uint256(bucketLevelBefore - bucketLevelAfter) == assert_uint256(amount - balanceFromInterestBefore)
            && balanceFromInterestAfter == 0
        : bucketLevelBefore == bucketLevelAfter 
            && balanceFromInterestAfter == assert_uint256(balanceFromInterestBefore - amount)
    );
}

// Possibility should not revert
rule functionsNotRevert(env e, method f, calldataarg args) 
    filtered { f -> !ALWAYS_REVERT_FUNCTIONS(f) } {

    f@withrevert(e, args);
    
    satisfy(!lastReverted);
}

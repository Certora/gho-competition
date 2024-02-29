import "./methods/GhoTokenHelperMethods.spec";

///////////////// METHODS //////////////////////

methods{

    //
    // Current contract
    //

    // GhoToken
    function mint(address account, uint256 amount) external;
    function burn(uint256 amount) external;
    function addFacilitator(address facilitator, string memory facilitatorLabel, 
        uint128 bucketCapacity) external;
    function removeFacilitator(address facilitator) external;
    function setFacilitatorBucketCapacity(address facilitator, uint128 newCapacity) external;
    function getFacilitator(address facilitator) external returns (IGhoToken.Facilitator) envfree;
    function getFacilitatorBucket(address facilitator) external returns (uint256, uint256) envfree;
    function getFacilitatorsList() external returns (address[]) envfree;

    // ERC20
    function approve(address spender, uint256 amount) internal returns (bool);
    function transfer(address to, uint256 amount) internal returns (bool);
    function transferFrom(address from, address to, uint256 amount) internal returns (bool);
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, 
        bytes32 r, bytes32 s) internal;
    function DOMAIN_SEPARATOR() internal returns (bytes32);
    function computeDomainSeparator() internal returns (bytes32);
    function _mint(address to, uint256 amount) internal;
    function _burn(address from, uint256 amount) internal;
    function totalSupply() external returns uint256 envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function nonces(address) external returns (uint256) envfree;

    // AccessControl
    function hasRole(bytes32 role, address account) internal returns (bool);
}

///////////////// DEFINITIONS /////////////////////

// Returns, whether a value is in the set.
definition inFacilitatorsList(bytes32 value) returns bool 
    = (ghostFacilitatorsListIndexes[value] != 0);

definition MINT_FUNCTION(method f) returns bool
    = f.selector == sig:mint(address, uint256).selector;

definition BURN_FUNCTION(method f) returns bool
    = f.selector == sig:burn(uint256).selector;

definition MINT_BURN_FUNCTIONS(method f) returns bool
    = MINT_FUNCTION(f) || BURN_FUNCTION(f);

definition PURE_VIEW_FUNCTIONS(method f) returns bool = f.isView || f.isPure;

////////////////// FUNCTIONS //////////////////////

function toBytes32(address value) returns bytes32 {
    return _GhoTokenHelper.toBytes32(value);
}

///////////////// GHOSTS & HOOKS //////////////////

//
// Ghost copy of `mapping(address => Facilitator) _facilitators`
//  .offset 0 - bucketCapacity
//  .offset 16 - bucketLevels
//  .offset 32 - label
//

ghost mathint ghostSumAllLevel {
    init_state axiom ghostSumAllLevel == 0;
}

ghost mapping (address => uint128) ghostBucketCapacity {
    init_state axiom forall address i. ghostBucketCapacity[i] == 0;
}

hook Sload uint128 capacity currentContract._facilitators[KEY address a].(offset 0) STORAGE {
    require(ghostBucketCapacity[a] == capacity);
}

hook Sstore currentContract._facilitators[KEY address a].(offset 0) uint128 capacity STORAGE {
    ghostBucketCapacity[a] = capacity;
}

ghost mapping (address => uint128) ghostBucketLevels {
    init_state axiom forall address i. ghostBucketLevels[i] == 0;
}

hook Sload uint128 level currentContract._facilitators[KEY address a].(offset 16) STORAGE {
    require(ghostBucketLevels[a] == level);
}

hook Sstore currentContract._facilitators[KEY address a].(offset 16) uint128 level (uint128 oldLevel) STORAGE {
    ghostBucketLevels[a] = level;
    ghostSumAllLevel = ghostSumAllLevel + level - oldLevel;
}

ghost mapping (address => bool) ghostInFacilitatorsMapping  {
    init_state axiom forall address i. ghostInFacilitatorsMapping[i] == false;
}

hook Sload uint256 stringLength currentContract._facilitators[KEY address a].(offset 32) STORAGE {
    if (stringLength > 0) {
        require(ghostInFacilitatorsMapping[a] == true);
    } else {
        require(ghostInFacilitatorsMapping[a] == false);
    }
}

hook Sstore currentContract._facilitators[KEY address a].(offset 32) uint256 stringLength STORAGE {
    if (stringLength > 0) {
        ghostInFacilitatorsMapping[a] = true;
    } else {
        ghostInFacilitatorsMapping[a] = false;
    }
}

//
// Ghost copy of `EnumerableSet.AddressSet _facilitatorsList`
//

ghost uint256 ghostFacilitatorsListLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom ghostFacilitatorsListLength < max_uint64;
    init_state axiom ghostFacilitatorsListLength == 0;
}

hook Sload uint256 length currentContract._facilitatorsList.(offset 0) STORAGE {
    require(ghostFacilitatorsListLength == length);
}

hook Sstore currentContract._facilitatorsList.(offset 0) uint256 newLength STORAGE {
    ghostFacilitatorsListLength = newLength;
}

ghost mapping(mathint => bytes32) ghostFacilitatorsListValues {
    init_state axiom forall mathint x. ghostFacilitatorsListValues[x] == to_bytes32(0);
}

hook Sload bytes32 val currentContract._facilitatorsList._inner._values[INDEX uint256 i] STORAGE {
    require(ghostFacilitatorsListValues[i] == val);
}

hook Sstore currentContract._facilitatorsList._inner._values[INDEX uint256 i] bytes32 val STORAGE {
    ghostFacilitatorsListValues[i] = val;
}

ghost mapping(bytes32 => uint256) ghostFacilitatorsListIndexes {
    init_state axiom forall bytes32 x. ghostFacilitatorsListIndexes[x] == 0;
}

hook Sload uint256 i currentContract._facilitatorsList._inner._indexes[KEY bytes32 val] STORAGE {
    require(ghostFacilitatorsListIndexes[val] == i);
}

hook Sstore currentContract._facilitatorsList._inner._indexes[KEY bytes32 val] uint256 i STORAGE {
    ghostFacilitatorsListIndexes[val] = i;
}

//
// Ghost copy of `ERC20.totalSupply`
//

ghost uint256 ghostTotalSupply {
    init_state axiom ghostTotalSupply == 0;
}

hook Sload uint256 val currentContract.totalSupply STORAGE {
    require(val == ghostTotalSupply);
} 

hook Sstore currentContract.totalSupply uint256 val STORAGE {
    ghostTotalSupply = val;
}

//
// Ghost copy of `ERC20.balanceOf`
//

ghost mapping (address => uint256) ghostBalanceOfMapping {
    init_state axiom forall address i. ghostBalanceOfMapping[i] == 0;
}

ghost mathint sumAllBalance {
    init_state axiom sumAllBalance == 0;
}

hook Sload uint256 balance currentContract.balanceOf[KEY address a] STORAGE {
    require(ghostBalanceOfMapping[a] == balance);
    require(to_mathint(balance) <= sumAllBalance);
} 

hook Sstore currentContract.balanceOf[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
    ghostBalanceOfMapping[a] = balance;
    sumAllBalance = sumAllBalance + balance - old_balance;
}

///////////////// ASSUME INVARIANTS ////////////////

// `EnumerableSet.AddressSet` internal coherency
invariant facilitatorsList_setInvariant()
    (forall uint256 i. i < ghostFacilitatorsListLength => to_mathint(ghostFacilitatorsListIndexes[ghostFacilitatorsListValues[i]]) == i + 1)
    && (forall bytes32 val. ghostFacilitatorsListIndexes[val] == 0 
        || (
            ghostFacilitatorsListValues[ghostFacilitatorsListIndexes[val] - 1] == val 
            && ghostFacilitatorsListIndexes[val] >= 1 && ghostFacilitatorsListIndexes[val] <= ghostFacilitatorsListLength
        )
    );

// `Facilitator.label` <=> `EnumerableSet.AddressSet` (`_indexes[value]`) coherency
invariant addr_in_set_iff_in_map(address facilitator)
    ghostInFacilitatorsMapping[facilitator] <=> inFacilitatorsList(toBytes32(facilitator)) {
        preserved {
            requireInvariant facilitatorsList_setInvariant();
        }
    }

// `Facilitator.label` <=> `ghoToken.getFacilitator(facilitator).label`
invariant valid_facilitatorLabel(address facilitator) 
    ghostInFacilitatorsMapping[facilitator] <=> _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0 {
        preserved {
            requireInvariant facilitatorsList_setInvariant();
            requireInvariant addr_in_set_iff_in_map(facilitator);
        }
    }

function assumeInvariants(address facilitator) {
    requireInvariant facilitatorsList_setInvariant();
    requireInvariant addr_in_set_iff_in_map(facilitator);
    requireInvariant valid_facilitatorLabel(facilitator);
}

///////////////// PROPERTIES //////////////////////

// Sum of balances is totalSupply()
invariant sumAllBalance_eq_totalSupply() 
    sumAllBalance == to_mathint(totalSupply());

// User's balance not greater than totalSupply()
invariant inv_balanceOf_leq_totalSupply(address user) 
    balanceOf(user) <= totalSupply() {
        preserved {
            requireInvariant sumAllBalance_eq_totalSupply();
        }
    }

// Sum of bucket levels is equals to totalSupply()
invariant total_supply_eq_sumAllLevel() 
    ghostSumAllLevel == to_mathint(totalSupply()) {
        preserved burn(uint256 amount) with (env e){
            requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
        }
    }

// The sum of bucket level is equal to the sum of GhoToken balances
invariant sumAllLevel_eq_sumAllBalance() 
    ghostSumAllLevel == sumAllBalance {
        preserved {
            requireInvariant sumAllBalance_eq_totalSupply();
        }
    }

// A facilitator with a positive bucket capacity exists in the _facilitators mapping
invariant inv_valid_capacity(address facilitator)
    ((_GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) > 0) 
        => ghostInFacilitatorsMapping[facilitator]);

// A facilitator with a positive bucket level exists in the _facilitators mapping
invariant inv_valid_level(address facilitator) 
    ((_GhoTokenHelper.getFacilitatorBucketLevel(facilitator) > 0) 
        => ghostInFacilitatorsMapping[facilitator]) {
        preserved{
            requireInvariant inv_valid_capacity(facilitator);
        }
    }

// Bucket level <= bucket capacity unless setFacilitatorBucketCapacity() lowered it
rule level_leq_capacity(address facilitator, method f) filtered { f -> !f.isView } {
    env e;
    calldataarg arg;

    assumeInvariants(facilitator);
    requireInvariant inv_valid_capacity(facilitator);
    require(_GhoTokenHelper.getFacilitatorBucketLevel(facilitator) 
        <= _GhoTokenHelper.getFacilitatorBucketCapacity(facilitator)); 
    
    f(e, arg);

    assert((f.selector != sig:setFacilitatorBucketCapacity(address,uint128).selector)
        => (_GhoTokenHelper.getFacilitatorBucketLevel(facilitator) 
            <= _GhoTokenHelper.getFacilitatorBucketCapacity(facilitator))
    );
}

// If Bucket level < bucket capacity then the first invocation of mint() succeeds after burn
//  unless setFacilitatorBucketCapacity() lowered bucket capacity or removeFacilitator() was called
rule mint_after_burn(method f) filtered { f -> !f.isView } {
    env e;
    calldataarg arg;
    uint256 amount_burn;
    uint256 amount_mint;
    address account;

    assumeInvariants(e.msg.sender);
    require(_GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender) 
        <= _GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender));
    require(amount_mint > 0);
    requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
    requireInvariant inv_valid_capacity(e.msg.sender);

    burn(e, amount_burn);
    f(e, arg);
    mint@withrevert(e, account, amount_mint);

    assert(((amount_mint <= amount_burn)
            && f.selector != sig:mint(address,uint256).selector
            && f.selector != sig:setFacilitatorBucketCapacity(address,uint128).selector
            && f.selector != sig:removeFacilitator(address).selector
            ) => !lastReverted), "mint failed";
}

// Burn after mint succeeds. BorrowLogic::executeRepa() executes the following code before
//  invocation of handleRepayment() 
rule burn_after_mint(method f) filtered { f -> !f.isView } {
    env e;
    uint256 amount;
    address account;

    requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
    
    mint(e, account, amount);
    transferFrom(e, account, e.msg.sender, amount);
    burn@withrevert(e, amount);

    assert(!lastReverted, "burn failed");
}

// BucketLevel remains unchanged after mint() followed by burn()
rule level_unchanged_after_mint_followed_by_burn() {
    env e;
    calldataarg arg;
    uint256 amount;
    address account;

    uint256 levelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);

    mint(e, account, amount);
    burn(e, amount);
    
    uint256 levelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
    
    assert(levelBefore == levelAfter);
}

// [9] BucketLevel changed correctly after mint
rule level_after_mint() {
    env e;
    calldataarg arg;
    uint256 amount;
    address account;

    uint256 levelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);

    mint(e, account, amount);

    uint256 levelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);

    assert(levelBefore + amount == to_mathint(levelAfter));

}

// [11] BucketLevel changed correctly after burn
rule level_after_burn() {
    env e;
    calldataarg arg;
    uint256 amount;

    uint256 levelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);

    burn(e, amount);
    
    uint256 levelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
    
    assert(to_mathint(levelBefore) == levelAfter + amount);
}

// Facilitator is valid after successful call to setFacilitatorBucketCapacity()
rule facilitator_in_list_after_setFacilitatorBucketCapacity() {
    env e;
    address facilitator;
    uint128 newCapacity;

    assumeInvariants(facilitator);

    setFacilitatorBucketCapacity(e, facilitator, newCapacity);
    
    assert(inFacilitatorsList(toBytes32(facilitator)));
}

// [21] _GhoTokenHelper.getFacilitatorBucketCapacity() called after setFacilitatorBucketCapacity() 
//  return the assign bucket capacity 
rule getFacilitatorBucketCapacity_after_setFacilitatorBucketCapacity() {
    env e;
    address facilitator;
    uint128 newCapacity;

    setFacilitatorBucketCapacity(e, facilitator, newCapacity);

    assert(_GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) == require_uint256(newCapacity));
}

// [13] Facilitator is valid after successful call to addFacilitator()
rule facilitator_in_list_after_addFacilitator() {
    env e;
    address facilitator;
    string label;
    uint128 capacity;

    assumeInvariants(facilitator);

    addFacilitator(e, facilitator, label, capacity);

    assert(inFacilitatorsList(toBytes32(facilitator)));
}

// [5] Facilitator is valid after successful call to mint() or burn()
rule facilitator_in_list_after_mint_and_burn(method f) {
    env e;
    calldataarg args;

    requireInvariant inv_valid_capacity(e.msg.sender);
    requireInvariant inv_valid_level(e.msg.sender);
    assumeInvariants(e.msg.sender);

    f(e,args);

    assert(((f.selector == sig:mint(address,uint256).selector) || (f.selector == sig:burn(uint256).selector)) 
        => inFacilitatorsList(toBytes32(e.msg.sender))
    );
}

// [16] Facilitator address is removed from list  (GhoToken._facilitatorsList._values) after calling removeFacilitator()
rule address_not_in_list_after_removeFacilitator(address facilitator) {
    env e;

    assumeInvariants(facilitator);
    
    bool before = inFacilitatorsList(toBytes32(facilitator));
    removeFacilitator(e, facilitator);
    
    assert(before && !inFacilitatorsList(toBytes32(facilitator)));
}

// [10] Balance changed correctly after `mint()`
rule balance_after_mint() {
    env e;
    address user;
    uint256 initBalance = balanceOf(user);
    uint256 initSupply = totalSupply();
    uint256 amount;

    requireInvariant sumAllBalance_eq_totalSupply();

    mint(e, user, amount);
    
    uint256 finBalance = balanceOf(user);
    uint256 finSupply = totalSupply();
    
    assert(initBalance + amount == to_mathint(finBalance));
    assert(initSupply + amount == to_mathint(finSupply));
}

// [12] Balance changed correctly after `burn()`
rule balance_after_burn() {
    env e;
    requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);

    uint256 initBalance = balanceOf(e.msg.sender);
    uint256 initSupply = totalSupply();
    uint256 amount;
    burn(e, amount);
    uint256 finBalance = balanceOf(e.msg.sender);
    uint256 finSupply = totalSupply();
    
    assert(to_mathint(initBalance) == finBalance + amount);
    assert(to_mathint(initSupply) == finSupply + amount);
}

// Proves that you can't mint more than the facilitator's remaining capacity
rule mintLimitedByFacilitatorRemainingCapacity() {
    env e;
    uint256 amount;

    mathint diff = _GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender) 
        - _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
    require(to_mathint(amount) > diff);
    
    address user;
    mint@withrevert(e, user, amount);
    
    assert(lastReverted);
}

// Proves that you can't burn more than the facilitator's current level
rule burnLimitedByFacilitatorLevel() {
    env e;

    require(_GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender) 
        > _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender));

    uint256 amount;
    require(amount > _GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender));
    burn@withrevert(e, amount);
    
    assert(lastReverted);
}

///////////////// ADDED PROPERTIES //////////////////////

// [1] addFacilitator() set label and bucket capacity 
rule addFacilitatorShouldSetLabelAndBucketCapacity(env e, address facilitator, string facilitatorLabel, uint128 bucketCapacity) {
    
    addFacilitator(e, facilitator, facilitatorLabel, bucketCapacity);

    assert(facilitatorLabel.length == _GhoTokenHelper.getFacilitatorsLabelLen(facilitator));
    assert(bucketCapacity == assert_uint128(_GhoTokenHelper.getFacilitatorBucketCapacity(facilitator)));
}

// [4] Mint and burn revert when amount is zero
rule mintBurnShouldRevertWhenZeroAmount(env e, address account, uint256 amount) {

    storage init = lastStorage;

    mint@withrevert(e, account, amount) at init;
    bool mintReverted = lastReverted;

    burn@withrevert(e, amount) at init;
    bool burnReverted = lastReverted;

    assert(amount == 0 => mintReverted && burnReverted);
}

// [6] Only account with `FACILITATOR_MANAGER_ROLE` can add or remove facilitators
rule onlyFacilitatorManagerCouldModifyFacilitatorList(env e, method f, calldataarg args)
    filtered { f -> !PURE_VIEW_FUNCTIONS(f) } {
    
    bool isManager = _GhoTokenHelper.hasFacilitatorManagerRole(e.msg.sender);
    uint256 listLengthBefore = ghostFacilitatorsListLength;

    f(e, args);
    
    assert(listLengthBefore != ghostFacilitatorsListLength => isManager);
}

// [7] Only account with `BUCKET_MANAGER_ROLE` can modify bucketCapacity
rule onlyBucketManagerCouldModifyBucketCapacity(env e, method f, calldataarg args, address facilitator)
    filtered { f -> !PURE_VIEW_FUNCTIONS(f) } {
    
    bool isManager = _GhoTokenHelper.hasBacketManagerRole(e.msg.sender);

    // Facilitator exists
    bool facilitatorExistBefore = _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0;

    uint256 bucketCapacityBefore = _GhoTokenHelper.getFacilitatorBucketCapacity(facilitator);
    f(e, args);
    uint256 bucketCapacityAfter = _GhoTokenHelper.getFacilitatorBucketCapacity(facilitator);

    // Facilitator was not removed
    bool facilitatorExistAfter = _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0;
    bool facilitatorExist = facilitatorExistBefore && facilitatorExistAfter;

    // Was modified
    bool bucketCapacityModified = bucketCapacityBefore != bucketCapacityAfter;

    assert(facilitatorExist && bucketCapacityModified => isManager);
}

// [8] Mint and burn affect only sender's facilitator
rule mintBurnAffectOnlySenderFacilitator(env e, method f, calldataarg args) 
    filtered { f -> MINT_BURN_FUNCTIONS(f) } {
    
    address other;
    require(other != e.msg.sender);

    uint128 otherBucketLevelBefore = ghostBucketLevels[other];

    f(e, args);

    uint128 otherBucketLevelAfter = ghostBucketLevels[other];

    assert(otherBucketLevelBefore == otherBucketLevelAfter);
}

// [14] Couln't add the same (with the same label) facilitator twice
rule facilitatorShouldNotAddedTwice(address facilitator, string facilitatorLabel, uint128 bucketCapacity) {

    env e1;
    addFacilitator(e1, facilitator, facilitatorLabel, bucketCapacity);

    env e2;
    addFacilitator@withrevert(e2, facilitator, facilitatorLabel, bucketCapacity);

    assert(lastReverted);
}

// [15] Couln't add facilitator with empty label
rule facilitatorAddedWithEmptyLabelShouldRevert(env e, address facilitator, string facilitatorLabel, uint128 bucketCapacity) {
    
    addFacilitator@withrevert(e, facilitator, facilitatorLabel, bucketCapacity);
    
    assert(facilitatorLabel.length == 0 => lastReverted);
}

// [17,20] Only existing facilitator could be removed or set bucket capacity
rule onlyExistingFacilitatorCouldBeRemovedOrSetBucketCapacity(address facilitator) {

    storage init = lastStorage;
    bool exist = _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0;

    env e1;
    removeFacilitator@withrevert(e1, facilitator) at init;
    bool removeReverted = lastReverted;

    env e2;
    uint128 newCapacity;
    setFacilitatorBucketCapacity@withrevert(e2, facilitator, newCapacity) at init;
    bool setBucketCapacityReverted = lastReverted;

    assert(!exist => removeReverted && setBucketCapacityReverted);
}

// [18] Only facilitator with zero bucketLevel could be removed
rule onlyFacilitatorWithZeroBucketLevelCouldBeRemoved(env e, address facilitator) {

    uint256 bucketLevel = _GhoTokenHelper.getFacilitatorBucketLevel(facilitator);

    removeFacilitator(e, facilitator);

    assert(bucketLevel == 0);
}

// [19] Facilitator's label empty after been removed
rule removeFacilitatorShouldEmptyLabel(env e, address facilitator) {

    bool existBefore = _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0;

    removeFacilitator(e, facilitator);

    bool existAfter = _GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0;

    assert(existBefore && !existAfter);
}

// [22] Prove view function work as expected 
rule gettersIntegrity(address facilitator) {

    assumeInvariants(facilitator);

    // getFacilitatorBucket()
    assert(assert_uint128(_GhoTokenHelper.getFacilitatorBucketCapacity(facilitator)) 
        == ghostBucketCapacity[facilitator]);
    assert(assert_uint128(_GhoTokenHelper.getFacilitatorBucketLevel(facilitator)) 
        == ghostBucketLevels[facilitator]);

    // getFacilitatorsList()
    assert(_GhoTokenHelper.getFacilitatorsListLen() == ghostFacilitatorsListLength);
}

// Possibility should not revert
rule functionsNotRevert(env e, method f, calldataarg args) {

    f@withrevert(e, args);
    
    satisfy(!lastReverted);
}

using GhoTokenHelper as GhoTokenHelper;

methods {
	function mint(address,uint256) external;
	function burn(uint256) external;
	function removeFacilitator(address) external;
	function setFacilitatorBucketCapacity(address,uint128) external;
	
	function hasRole(bytes32, address) external returns bool envfree;

	function FACILITATOR_MANAGER_ROLE() external returns bytes32 envfree;
	function BUCKET_MANAGER_ROLE() external returns bytes32 envfree;

	function getFacilitator(address) external returns IGhoToken.Facilitator envfree;
	function getFacilitatorBucket(address) external returns (uint256, uint256) envfree;
	function getFacilitatorsList() external returns address[] envfree;

	function totalSupply() external returns uint256 envfree;
	function balanceOf(address) external returns (uint256) envfree;

	// Helper getters
	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorsLableLen(address facilitator) external  returns (uint256) envfree;
	function GhoTokenHelper.toBytes32(address) external returns (bytes32) envfree;
}


// GHOST COPIES:
// For every storage variable we add a ghost field that is kept synchronized by hooks.
// The ghost fields can be accessed by the spec, even inside quantifiers.

// ghost field for the values array
ghost mapping(mathint => bytes32) ghostValues {
    init_state axiom forall mathint x. ghostValues[x] == to_bytes32(0);
}
// ghost field for the indexes map
ghost mapping(bytes32 => uint256) ghostIndexes {
    init_state axiom forall bytes32 x. ghostIndexes[x] == 0;
}
// ghost field for the length of the values array (stored in offset 0)
ghost uint256 ghostLength {
    // assumption: it's infeasible to grow the list to these many elements.
    axiom ghostLength < max_uint256;
}

// HOOKS
// Store hook to synchronize ghostLength with the length of the _facilitatorsList._inner._values array. 
// We need to use (offset 0) here, as there is no keyword yet to access the length.
hook Sstore currentContract._facilitatorsList.(offset 0) uint256 newLength STORAGE {
    ghostLength = newLength;
}
// Store hook to synchronize ghostValues array with set._inner._values.
hook Sstore currentContract._facilitatorsList._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    ghostValues[index] = newValue;
}
// Store hook to synchronize ghostIndexes array with set._inner._indexes.
hook Sstore currentContract._facilitatorsList._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    ghostIndexes[value] = newIndex;
}

// The load hooks can use require to ensure that the ghost field has the same information as the storage.
// The require is sound, since the store hooks ensure the contents are always the same.  However we cannot
// prove that with invariants, since this would require the invariant to read the storage for all elements
// and neither storage access nor function calls are allowed in quantifiers.
//
// By following this simple pattern it is ensured that the ghost state and the storage are always the same
// and that the solver can use this knowledge in the proofs.

// Load hook to synchronize ghostLength with the length of the set._inner._values array. 
// Again we use (offset 0) here, as there is no keyword yet to access the length.
hook Sload uint256 length currentContract._facilitatorsList.(offset 0) STORAGE {
    require ghostLength == length;
}
hook Sload bytes32 value currentContract._facilitatorsList._inner._values[INDEX uint256 index] STORAGE {
    require ghostValues[index] == value;
}
hook Sload uint256 index currentContract._facilitatorsList._inner._indexes[KEY bytes32 value] STORAGE {
    require ghostIndexes[value] == index;
}


/********* Ghosts ***************/
// Sum of all balances[a]
ghost mathint sumAllBalance {
    init_state axiom sumAllBalance == 0;
}

// Sum of facilitators' bucket levels 
ghost mathint sumAllLevel {
    init_state axiom sumAllLevel == 0;
}

// Indication if facilitator is in _facilitators mapping
ghost mapping (address => bool) inFacilitatorsMapping  {
    init_state axiom forall address f. !inFacilitatorsMapping[f];
}


hook Sstore balanceOf[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
   sumAllBalance = sumAllBalance + balance - old_balance;
}

hook Sload uint256 balance balanceOf[KEY address a] STORAGE {
    require to_mathint(balance) <= sumAllBalance;
} 


/**
 * @title Sum of facilitators' bucket levels 
 * @dev Sample stores to  _facilitators[*].bucketLevel
 * @dev first field of struct Facilitator is uint128 so offset 16 is used  
 **/
hook Sstore _facilitators[KEY address a].(offset 16) uint128 level (uint128 old_level)   STORAGE {
   	sumAllLevel = sumAllLevel+ level - old_level;
}

hook Sstore _facilitators[KEY address a].(offset 32) uint256 string_length (uint256 old_length)   STORAGE {
  if (string_length > 0) {
	inFacilitatorsMapping[a] = true;
  }
  else {
	inFacilitatorsMapping[a] = false;
  }
	
}

hook Sload  uint256 string_length _facilitators[KEY address a].(offset 32)    STORAGE {
  if (string_length > 0) {
	require inFacilitatorsMapping[a];
  }
  else {
	require !inFacilitatorsMapping[a];
  }
	
}

//
// Helper Functions
//
function toBytes32(address value) returns bytes32 {
	return GhoTokenHelper.toBytes32(value);
}

// Returns, whether a value is in the set.
definition inFacilitatorsList(bytes32 value) returns bool = (ghostIndexes[value] != 0);

//
// Invariants
//

/**
* @title AddressSet internal coherency
* @dev A facilitator address exists in AddressSet list (GhoToken._facilitatorsList._values)
* @dev if and only if it exists in AddressSet mapping (GhoToken._facilitatorsList._indexes)
* @notice set_facilitatorList contains ghosts, hooks and invariant of the valid state of _facilitatorsList base on enumberableSet spec https://github.com/Certora/Examples/tree/master/CVLByExample/QuantifierExamples
**/
invariant facilitatorsList_setInvariant()
    (forall uint256 index. index < ghostLength => to_mathint(ghostIndexes[ghostValues[index]]) == index + 1)
    && (forall bytes32 value. ghostIndexes[value] == 0 || 
         (ghostValues[ghostIndexes[value] - 1] == value && ghostIndexes[value] >= 1 && ghostIndexes[value] <= ghostLength));

// INV #2
/**
* @title User's balance not greater than totalSupply()
*/
invariant inv_balanceOf_leq_totalSupply(address user)
	balanceOf(user) <= totalSupply()
	{
		preserved {
			requireInvariant sumAllBalance_eq_totalSupply();
		}
	}

// INV #3
/**
 * @title Sum of bucket levels is equals to GhoToken::totalSupply()
 **/
invariant total_supply_eq_sumAllLevel()
		sumAllLevel == to_mathint(totalSupply()) 
	{
	  preserved burn(uint256 amount) with (env e){
			requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
		}
	}


// INV #4
/**
 * @title Sum of balances is GhoToke::totalSupply()
 **/
invariant sumAllBalance_eq_totalSupply()
	sumAllBalance == to_mathint(totalSupply());
	

// INV #5
/**
 * @title The sum of bucket level is equal to the sum of GhoToken balances
 * @dev This invariant can be deduced from sumAllBalance_eq_totalSupply and total_supply_eq_sumAllLevel
 * @dev requireInvariant of EITHER sumAllBalance_eq_totalSupply() OR total_supply_eq_sumAllLevel() suffuces for the proof
 **/
invariant sumAllLevel_eq_sumAllBalance()
	sumAllLevel == sumAllBalance
	  	{
			preserved {
			requireInvariant sumAllBalance_eq_totalSupply();
		}
	}



// INV #6
/**
* @title A facilitator with a positive bucket capacity exists in the _facilitators mapping
*/
invariant inv_valid_capacity(address facilitator)
	((GhoTokenHelper.getFacilitatorBucketCapacity(facilitator)>0) => inFacilitatorsMapping[facilitator] );

// INV #7
/**
* @title A facilitator with a positive bucket level exists in the _facilitators mapping
*/
invariant inv_valid_level(address facilitator)
	((GhoTokenHelper.getFacilitatorBucketLevel(facilitator)>0) => inFacilitatorsMapping[facilitator] )
	{
		preserved{
			requireInvariant inv_valid_capacity(facilitator);
		}
	}

// INV #9
/**
* @title GhoToken mapping-AddressSet coherency (1)
* @dev A facilitator address that exists in GhoToken Facilitator mapping (GhoToken._facilitators)
* @dev if and only if it exists in GhoToken  AddressSet (GhoToken._facilitatorsList._indexes)
*/

invariant addr_in_set_iff_in_map(address facilitator)
	inFacilitatorsMapping[facilitator] <=> inFacilitatorsList(toBytes32(facilitator))
	{
		preserved {
 		requireInvariant facilitatorsList_setInvariant();
		}
	}

// INV #10
/**
* @title validity of a facilitator struct
* @dev A facilitator address that exists in GhoToken Facilitator mapping (GhoToken._facilitators)
* @dev if and only if it had a non empty label 
*/	

invariant valid_facilitatorLabel(address facilitator) 
	inFacilitatorsMapping[facilitator] <=> GhoTokenHelper.getFacilitatorsLableLen(facilitator) > 0 
	{
		preserved {
			requireInvariant facilitatorsList_setInvariant();
			requireInvariant addr_in_set_iff_in_map(facilitator);
		}
	}


//
// Rules
//

function assumeInvariants(address facilitator) {
	requireInvariant facilitatorsList_setInvariant();
	requireInvariant addr_in_set_iff_in_map(facilitator);
	requireInvariant valid_facilitatorLabel(facilitator);
}

/**
* @title Bucket level <= bucket capacity unless setFacilitatorBucketCapacity() lowered it
*/
rule level_leq_capacity(address facilitator, method f) filtered {f -> !f.isView}{

	env e;
	calldataarg arg;
	assumeInvariants(facilitator);
	requireInvariant inv_valid_capacity(facilitator);
	require GhoTokenHelper.getFacilitatorBucketLevel(facilitator) <= GhoTokenHelper.getFacilitatorBucketCapacity(facilitator); 
	f(e, arg);
	assert ((f.selector != sig:setFacilitatorBucketCapacity(address,uint128).selector)
		=>	(GhoTokenHelper.getFacilitatorBucketLevel(facilitator) <= GhoTokenHelper.getFacilitatorBucketCapacity(facilitator)));
		
}

/**
* @notice If Bucket level < bucket capacity then the first invocation of mint() succeeds after burn
* @notice unless setFacilitatorBucketCapacity() lowered bucket capacity or removeFacilitator() was called
*/
rule mint_after_burn(method f) filtered {f -> !f.isView}
{
	env e;
	calldataarg arg;
	uint256 amount_burn;
	uint256 amount_mint;
	address account;
	
	assumeInvariants(e.msg.sender);
	require GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender) <= GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender);
	require amount_mint > 0;

	requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
	requireInvariant inv_valid_capacity(e.msg.sender);

	burn(e, amount_burn);
	f(e, arg);
	mint@withrevert(e, account, amount_mint);
	assert (((amount_mint <= amount_burn)
			&& f.selector != sig:mint(address,uint256).selector
			&& f.selector != sig:setFacilitatorBucketCapacity(address,uint128).selector
			&& f.selector != sig:removeFacilitator(address).selector
			)	=> !lastReverted), "mint failed";
}

/**
* @title Burn after mint succeeds
* @dev BorrowLogic::executeRepa() executes the following code before invocation of handleRepayment()
* @dev safeTransferFrom(msg.sender, reserveCache.aTokenAddress, paybackAmount);
*/
rule burn_after_mint(method f) filtered {f -> !f.isView}
{
	env e;
	uint256 amount;
	address account;

	requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
	
	mint(e, account, amount);
	transferFrom(e, account, e.msg.sender, amount);
	burn@withrevert(e, amount);
	assert !lastReverted, "burn failed";
}

/**
* @title BucketLevel remains unchanged after mint() followed by burn()
*/
rule level_unchanged_after_mint_followed_by_burn()
{
	env e;
	calldataarg arg;
	uint256 amount;
	address account;

	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	mint(e, account, amount);
	burn(e, amount);
	uint256 leveAfter = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	assert levelBefore == leveAfter;

}

rule level_after_mint()
{
	env e;
	calldataarg arg;
	uint256 amount;
	address account;

	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	mint(e, account, amount);
	uint256 leveAfter = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	assert levelBefore + amount == to_mathint(leveAfter);

}

rule level_after_burn()
{
	env e;
	calldataarg arg;
	uint256 amount;

	uint256 levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	burn(e, amount);
	uint256 leveAfter = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	assert to_mathint(levelBefore) == leveAfter + amount;

}

/**
* @title Facilitator is valid before and after successful call to setFacilitatorBucketCapacity()
*/
rule facilitator_in_list_after_setFacilitatorBucketCapacity(){

	env e;
	address facilitator;
	uint128 newCapacity;

	assumeInvariants(facilitator);

	bool inListBefore = inFacilitatorsList(toBytes32(facilitator));

	setFacilitatorBucketCapacity(e, facilitator, newCapacity);
	
	assert inListBefore && inFacilitatorsList(toBytes32(facilitator));
}

/**
* @title GhoTokenHelper.getFacilitatorBucketCapacity() called after setFacilitatorBucketCapacity() retrun the assign bucket capacity
*/
rule getFacilitatorBucketCapacity_after_setFacilitatorBucketCapacity(){

	env e;
	address facilitator;
	uint128 newCapacity;

	setFacilitatorBucketCapacity(e, facilitator, newCapacity);
	assert GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) == require_uint256(newCapacity);
}

/**
* @title Facilitator is valid before and after successful call to mint() or burn()
*/
rule facilitator_in_list_mint_and_burn(method f) filtered { f -> 
	f.selector == sig:mint(address,uint256).selector || 
		f.selector == sig:burn(uint256).selector
}
{
	env e;
	calldataarg args;
	requireInvariant inv_valid_capacity(e.msg.sender);
	requireInvariant inv_valid_level(e.msg.sender);
	assumeInvariants(e.msg.sender);

	bool inListBefore = inFacilitatorsList(toBytes32(e.msg.sender));

	f(e,args);

	assert inListBefore && inFacilitatorsList(toBytes32(e.msg.sender));
}

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
	assert initBalance + amount == to_mathint(finBalance);
	assert initSupply + amount == to_mathint(finSupply);
}

rule balance_after_burn() {
	
	env e;
	requireInvariant inv_balanceOf_leq_totalSupply(e.msg.sender);
	uint256 initBalance = balanceOf(e.msg.sender);
	uint256 initSupply = totalSupply();
	uint256 amount;
	burn(e, amount);
	uint256 finBalance = balanceOf(e.msg.sender);
	uint256 finSupply = totalSupply();
	assert to_mathint(initBalance) == finBalance + amount;
	assert to_mathint(initSupply) == finSupply + amount ;
}


/**
* @title Proves that you can't mint more than the facilitator's remaining capacity
**/
rule mintLimitedByFacilitatorRemainingCapacity() {
	env e;

	uint256 amount;
	require(to_mathint(amount) > (GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender) - GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender)));
	address user;
	mint@withrevert(e, user, amount);
	assert lastReverted;
}

/**
* @title Proves that you can't burn more than the facilitator's current level
**/
rule burnLimitedByFacilitatorLevel() {
	env e;
	require(GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender) > GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender));

	uint256 amount;
	require(amount > GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender));
	burn@withrevert(e, amount);
	assert lastReverted;
}

/**
* @title Facilitator address is removed from the list (GhoToken._facilitatorsList._values) 
		after a successful call to removeFacilitator(). Also, this facilitator must 
		be in the list prior to the call and it is the only facilitator being removed.
**/
rule address_not_in_list_after_removeFacilitator(address facilitator) {
	env e;
	assumeInvariants(facilitator);
    uint256 preFacilitatorsCount = ghostLength;
	
	bool inListBefore = inFacilitatorsList(toBytes32(facilitator));
   
	removeFacilitator(e, facilitator);
	
    assert inListBefore && !inFacilitatorsList(toBytes32(facilitator)) &&
            assert_uint256(preFacilitatorsCount - 1) == ghostLength;
}

/**
@title A facilitator can be removed successfully only if its bucket level is zero.
*/
rule can_only_removeFacilitator_with_empty_bucket(address facilitator) {
    env e;
	assumeInvariants(facilitator);

	uint256 bucketLevelBefore = GhoTokenHelper.getFacilitatorBucketLevel(facilitator);
	
	removeFacilitator(e, facilitator);

	assert bucketLevelBefore == 0;
}

/**
	@title Proves that removeFacilitator enables removing facilitators with
	any non-empty labels' lengths.
*/
rule removesFacilitator_succeeds_for_any_non_empty_label() {
    env e;
	address facilitator;

	assumeInvariants(facilitator);

	// assume facilitator is in list
    require(inFacilitatorsList(toBytes32(facilitator)));

	// assume facilitator's bucket level is zero
	require(GhoTokenHelper.getFacilitatorBucketLevel(facilitator) == 0);

	// assume e.msg.sender is a facilitator manager
	require(hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender));
	
	// exclude reverts due to non-payability
	require(e.msg.value == 0);

	uint256 labelLength = GhoTokenHelper.getFacilitatorsLableLen(facilitator);

	removeFacilitator@withrevert(e, facilitator);
    
    assert !lastReverted <=> labelLength > 0;
}

definition facilitatorManagerRoleFunction(method f) returns bool = 
    f.selector == sig:addFacilitator(address,string,uint128).selector ||
        f.selector == sig:removeFacilitator(address).selector;

definition bucketManagerRoleFunction(method f) returns bool = 
    f.selector == sig:setFacilitatorBucketCapacity(address,uint128).selector;

/**
* @title Proves that all the functions except addFacilitator and removeFacilitator (resp. setFacilitatorBucketCapacity)
         can succeed without reverting while msg.sender does not have a role of facilitator (resp. bucket) manager.
*/
rule canSucceedWithoutManagerRole(method f) filtered { 
    f -> !facilitatorManagerRoleFunction(f) && !bucketManagerRoleFunction(f)
 } 
 {
	env e;
    calldataarg args;

	bool hasFacilitatorManagerRoleBefore = hasRole(e, FACILITATOR_MANAGER_ROLE(), e.msg.sender);
	bool hasBucketManagerRoleBefore = hasRole(BUCKET_MANAGER_ROLE(), e.msg.sender);

    f@withrevert(e, args);

    satisfy !lastReverted && 
		!hasFacilitatorManagerRoleBefore && 
			!hasBucketManagerRoleBefore;
}

/**
* @title Facilitator is valid after a successful call to addFacilitator() and must not be
* in the list prior to the successful call.
*/
rule facilitator_in_list_after_addFacilitator() {
	env e;
	address facilitator;
	string facilitatorLabel;
	uint128 bucketCapacity;

	assumeInvariants(facilitator);
    uint256 preFacilitatorsCount = ghostLength;

	bool inListBefore = inFacilitatorsList(toBytes32(facilitator));
   
	addFacilitator(e, facilitator, facilitatorLabel, bucketCapacity);

    uint256 postBucketCapacity = GhoTokenHelper.getFacilitatorBucketCapacity(facilitator);
    uint256 postLabelLength = GhoTokenHelper.getFacilitatorsLableLen(facilitator);

	assert !inListBefore && inFacilitatorsList(toBytes32(facilitator)) && 
        facilitatorLabel.length == postLabelLength && 
        assert_uint256(bucketCapacity) == postBucketCapacity && 
        ghostLength == assert_uint256(preFacilitatorsCount + 1);
}

/**
	@title Proves that addFacilitator reverts iff the given facilitator's label
	is empty. Effectively proves that addFacilitator enables adding facilitators with
	any non-empty labels' lengths.
*/
rule addFacilitator_enables_any_non_empty_label() {
    env e;
	address facilitator;
	string facilitatorLabel;
	uint128 bucketBapacity;

	assumeInvariants(facilitator);

	// assume facilitator is not in list
    require(!inFacilitatorsList(toBytes32(facilitator)));

	// assume e.msg.sender is a facilitator manager
	require(hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender));
	
	// exclude reverts due to non-payability
	require(e.msg.value == 0);

	addFacilitator@withrevert(e, facilitator, facilitatorLabel, bucketBapacity);
    
    assert lastReverted <=> facilitatorLabel.length == 0;
}

/**
  @title When a Facilitator's bucket level becomes greater than its bucket capacity, that
  facilitator can only decrease its bucket level.
  @credit Czar102
*/ 
rule facilitator_level_can_only_decrease_when_gt_capacity(address facilitator, method f) filtered {
    f -> !f.isView
    }
    {
	env e;
	calldataarg arg;
	assumeInvariants(facilitator);
	requireInvariant inv_valid_capacity(facilitator);
	uint init_level = GhoTokenHelper.getFacilitatorBucketLevel(facilitator);
    // Notice: strict inequality is a feasible post-state e.g. of setFacilitatorBucketCapacity
	require init_level >= GhoTokenHelper.getFacilitatorBucketCapacity(facilitator);

	f(e, arg);

	assert GhoTokenHelper.getFacilitatorBucketLevel(facilitator) <= init_level;
}

/**
@title Proves that functions that are expected to be called successfully only by the
bucket/facilitator manager role can only be called by that role.
*/
rule managerOnlyFunction(method f) filtered {
	f -> bucketManagerRoleFunction(f) || facilitatorManagerRoleFunction(f)
}
{
	env e;
	calldataarg args;

	bool hasRoleBefore;
	
	if(bucketManagerRoleFunction(f)) {
		hasRoleBefore = hasRole(BUCKET_MANAGER_ROLE(), e.msg.sender);
	} else {
		assert(facilitatorManagerRoleFunction(f));
		hasRoleBefore = hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender);
	}

	f(e, args);

	assert hasRoleBefore, 
		"Should have only been called successfully by a manager role";
}

/**
	Proves that non-view functions do not change roles
	with the exception of grantRole, renounceRole, and revokeRole.
*/
rule functionDoesNotChangeRoles(method f) filtered { 
	f -> !f.isView && f.selector != sig:grantRole(bytes32,address).selector &&
		f.selector != sig:renounceRole(bytes32,address).selector && 
		f.selector != sig:revokeRole(bytes32,address).selector
	} {
	env e;
	calldataarg args;
	bytes32 role;
	
	bool hasRoleBefore = hasRole(role, e.msg.sender);

	f(e, args);

	assert hasRole(role, e.msg.sender) == hasRoleBefore,
		"Should not have changed roles";
}


/// candidate rules ///


//0xAzezSec
rule updateCapacity(method f)filtered{f-> f.selector != sig:removeFacilitator(address).selector && f.selector !=sig:addFacilitator(address,string,uint128).selector}{
    uint256 newFee;
    env e; calldataarg args;
	require inFacilitatorsList(toBytes32(e.msg.sender));

    uint256 _capacity = GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender);
    f(e,args);
    uint256 capacity_ = GhoTokenHelper.getFacilitatorBucketCapacity(e.msg.sender);

    assert (_capacity != capacity_ => (f.selector == sig:setFacilitatorBucketCapacity(
    address,
    uint128 ).selector) ),"incorrect update for the capacity value ";
}
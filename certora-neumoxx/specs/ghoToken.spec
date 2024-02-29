using GhoTokenHelper as GhoTokenHelper;

methods{
	function mint(address,uint256) external;
	function burn(uint256) external;
	function removeFacilitator(address) external;
	function setFacilitatorBucketCapacity(address,uint128) external;

	function totalSupply() external returns uint256 envfree;
	function balanceOf(address) external returns (uint256) envfree;

	// Helper getters
	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorLabel(address) external returns string envfree;
	function GhoTokenHelper.getFacilitatorsLableLen(address facilitator) external  returns (uint256) envfree;
	function GhoTokenHelper.stringsAreEqual(string,string) external returns bool envfree;
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
    (forall uint256 index. 0 <= index && index < ghostLength => to_mathint(ghostIndexes[ghostValues[index]]) == index + 1)
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
* @title Facilitator is valid after successful call to setFacilitatorBucketCapacity()
*/
rule facilitator_in_list_after_setFacilitatorBucketCapacity(){

	env e;
	address facilitator;
	uint128 newCapacity;

	assumeInvariants(facilitator);

	setFacilitatorBucketCapacity(e, facilitator, newCapacity);
	
	assert inFacilitatorsList(toBytes32(facilitator));
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
* @title Facilitator is valid after successful call to addFacilitator()
*/
rule facilitator_in_list_after_addFacilitator(){

	env e;
	address facilitator;
	string label;
	uint128 capacity;

	assumeInvariants(facilitator);

	addFacilitator(e, facilitator, label, capacity);

	assert inFacilitatorsList(toBytes32(facilitator));
}

/**
* @title Facilitator values are stored correctly after the call
*/
rule addFacilitatorConsistencyCheck(){

	env e;
	address facilitator;
	string label = "test";
	uint128 capacity;

	assumeInvariants(facilitator);

	string initialLabel = GhoTokenHelper.getFacilitatorLabel(facilitator);
	uint256 initialLabelLength = initialLabel.length;
	require initialLabelLength <= 2;

	require GhoTokenHelper.getFacilitatorBucketLevel(facilitator) == 0;

	addFacilitator@withrevert(e, facilitator, label, capacity);
	bool lastRev = lastReverted;
	bool hasProperRole = hasRole(e, FACILITATOR_MANAGER_ROLE(e), e.msg.sender);

	assert (
		e.msg.value > 0 ||
		initialLabelLength > 0 ||
		!hasProperRole
	) <=> lastRev;
	assert !lastRev => (
		GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) == assert_uint256(capacity) &&
		GhoTokenHelper.getFacilitatorBucketLevel(facilitator) == 0 &&
		GhoTokenHelper.stringsAreEqual(label, GhoTokenHelper.getFacilitatorLabel(facilitator))
	);
}

/**
* @title Facilitator label cannot be empty
*/
rule addFacilitatorEmptyLabelMakesRevert(){
	env e;
	address facilitator;
	string label;
	uint128 capacity;

	require label.length <= 2;

	addFacilitator(e, facilitator, label, capacity);

	assert label.length > 0;
}

/**
* @notice Consistency check for the execution of function removeFacilitator
*/
rule removeFacilitatorConsistencyCheck(){

	env e;
	address facilitator;

	string initialLabel = GhoTokenHelper.getFacilitatorLabel(facilitator);
	uint256 initialLabelLength = initialLabel.length;
	require initialLabelLength <= 2;

	assumeInvariants(facilitator);

	uint256 bucketLevel = GhoTokenHelper.getFacilitatorBucketLevel(facilitator);

	removeFacilitator@withrevert(e, facilitator);
	bool lastRev = lastReverted;

	bool hasProperRole = hasRole(e, FACILITATOR_MANAGER_ROLE(e), e.msg.sender);

	assert (
		e.msg.value > 0 ||
		bucketLevel > 0 ||
		initialLabelLength == 0 ||
		!hasProperRole
	) <=> lastRev;
	assert !lastRev => (
		GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) == 0 &&
		GhoTokenHelper.getFacilitatorBucketLevel(facilitator) == 0
	);
}

/**
* @notice Consistency check for the execution of function setFacilitatorBucketCapacity
*/
rule setFacilitatorBucketCapacityConsistencyCheck(){

	env e;
	address facilitator;
	uint128 newCapacity;

	assumeInvariants(facilitator);

	string initialLabel = GhoTokenHelper.getFacilitatorLabel(facilitator);
	uint256 initialLabelLength = initialLabel.length;
	require initialLabelLength <= 2;

	bool hasProperRole = hasRole(e, BUCKET_MANAGER_ROLE(e), e.msg.sender);

	setFacilitatorBucketCapacity@withrevert(e, facilitator, newCapacity);
	bool lastRev = lastReverted;

	assert (
		e.msg.value > 0 ||
		initialLabelLength == 0 ||
		!hasProperRole
	) <=> lastRev;
	assert !lastRev => (
		GhoTokenHelper.getFacilitatorBucketCapacity(facilitator) == assert_uint256(newCapacity)
	);
}

/**
* @notice Consistency check for the execution of function getFacilitatorBucketConsistencyCheck
**/
rule getFacilitatorBucketConsistencyCheck() {

	env e;
	address facilitator;
	uint256 bucketCapacity;
	uint256 bucketLevel;
	uint256 bucketCapacity2;
	uint256 bucketLevel2;

	assumeInvariants(facilitator);

	bucketCapacity, bucketLevel = getFacilitatorBucket@withrevert(e, facilitator);
	bucketCapacity2, bucketLevel2 = getFacilitatorBucketHarness@withrevert(e, facilitator);
	bool lastRev = lastReverted;

	assert (
		e.msg.value > 0
	) <=> lastRev;
	assert !lastRev => (
		bucketCapacity == bucketCapacity2 && 
		bucketLevel == bucketLevel2
	);
}

/**
* @notice Consistency check for the execution of function mint
**/
rule mintConsistencyCheck() {

	env e;
	uint256 bucketCapacity;
	uint256 bucketLevel;
	uint256 bucketCapacity2;
	uint256 bucketLevel2;
	address account;
	uint256 amount;

	assumeInvariants(e.msg.sender);

	bucketCapacity, bucketLevel = getFacilitatorBucket(e, e.msg.sender);
	uint256 balancePre = balanceOf(e, account);
	uint256 supplyPre = totalSupply(e);

	uint256 finalBalance = require_uint256(balancePre + amount);
	mathint finalBucketLevel = bucketLevel + amount;
	uint256 finalSupply = require_uint256(supplyPre + amount);

	mint@withrevert(e, account, amount);

	bool lastRev = lastReverted;
	uint256 balancePost = balanceOf(e, account);
	uint256 supplyPost = totalSupply(e);
	bucketCapacity2, bucketLevel2 = getFacilitatorBucket(e, e.msg.sender);
	uint256 newBucketLevel = require_uint256(bucketLevel + amount);

	assert (
		e.msg.value > 0 ||
		amount == 0 ||
		to_mathint(bucketCapacity) < finalBucketLevel ||
		finalBucketLevel > max_uint256
	) <=> lastRev;
	assert !lastRev => (
		balancePost == finalBalance && 
		supplyPost == finalSupply && 
		bucketLevel2 == newBucketLevel
	);
}

/**
* @notice Consistency check for the execution of function burn
**/
rule burnConsistencyCheck() {

	env e;
	uint256 bucketCapacity;
	uint256 bucketLevel;
	uint256 bucketCapacity2;
	uint256 bucketLevel2;
	uint256 amount;

	assumeInvariants(e.msg.sender);

	bucketCapacity, bucketLevel = getFacilitatorBucket(e, e.msg.sender);
	uint256 balancePre = balanceOf(e, e.msg.sender);
	uint256 supplyPre = totalSupply(e);
	burn@withrevert(e, amount);
	bool lastRev = lastReverted;
	uint256 balancePost = balanceOf(e, e.msg.sender);
	uint256 supplyPost = totalSupply(e);
	bucketCapacity2, bucketLevel2 = getFacilitatorBucket(e, e.msg.sender);
	uint256 newBucketLevel = require_uint256(bucketLevel - amount);

	assert (
		e.msg.value > 0 ||
		amount == 0 ||
		balancePre < amount ||
		bucketLevel < amount
	) <=> lastRev;
	assert !lastRev => (
		balancePost == require_uint256(balancePre - amount) && 
		supplyPost == require_uint256(supplyPre - amount) && 
		bucketLevel2 == newBucketLevel
	);
}

/**
* @title Facilitator is valid after successful call to mint() or burn()
*/
rule facilitator_in_list_after_mint_and_burn(method f){

	env e;
	calldataarg args;
	requireInvariant inv_valid_capacity(e.msg.sender);
	requireInvariant inv_valid_level(e.msg.sender);
	assumeInvariants(e.msg.sender);

	f(e,args);
	assert (((f.selector == sig:mint(address,uint256).selector) || (f.selector == sig:burn(uint256).selector)) => inFacilitatorsList(toBytes32(e.msg.sender)));
}

/**
* @title Facilitator address is removed from list  (GhoToken._facilitatorsList._values) after calling removeFacilitator()
**/
rule address_not_in_list_after_removeFacilitator(address facilitator){
	env e;
	assumeInvariants(facilitator);
	bool before =  inFacilitatorsList(toBytes32(facilitator));
	removeFacilitator(e, facilitator);
	assert before && !inFacilitatorsList(toBytes32(facilitator));
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

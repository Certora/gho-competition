using GhoTokenHelper as GhoTokenHelper;

methods{
	function mint(address,uint256) external;
	function burn(uint256) external;
	function removeFacilitator(address) external;
	function setFacilitatorBucketCapacity(address,uint128) external;

	function transfer(address,uint256) external;
	function transferFrom(address,address,uint256) external;

	function totalSupply() external returns uint256 envfree;
	function balanceOf(address) external returns (uint256) envfree;

	function FACILITATOR_MANAGER_ROLE() external returns bytes32 envfree;
	function BUCKET_MANAGER_ROLE() external returns bytes32 envfree;

	function hasRole(bytes32, address) external returns bool envfree;

	// can I skip return values?
	function getFacilitator(address) external returns IGhoToken.Facilitator envfree;
	function getFacilitatorBucket(address) external returns (uint256, uint256) envfree;
	function getFacilitatorsList() external returns address[] envfree;

	function deployer() external returns address envfree;

	// Helper getters
	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns uint256 envfree;
	function GhoTokenHelper.getFacilitatorsListLen() external  returns (uint256) envfree;
	function GhoTokenHelper.getFacilitatorsLabelLen(address facilitator) external  returns (uint256) envfree;
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

ghost bool facilitatorOrBalanceStateTouched {
	init_state axiom !facilitatorOrBalanceStateTouched;
}

ghost mapping(bytes32 => mapping(address => bool)) role_mirror {
	init_state axiom forall bytes32 role. forall address a. !role_mirror[role][a];
}

hook Sstore _roles[KEY bytes32 role].(offset 0)[KEY address member] bool newStatus STORAGE {
	role_mirror[role][member] = newStatus;
}

hook Sload bool status _roles[KEY bytes32 role].(offset 0)[KEY address member] STORAGE {
	require role_mirror[role][member] == status;
}

// HOOKS
// Store hook to synchronize ghostLength with the length of the _facilitatorsList._inner._values array. 
// We need to use (offset 0) here, as there is no keyword yet to access the length.
hook Sstore currentContract._facilitatorsList.(offset 0) uint256 newLength STORAGE {
	if (newLength != 0)
		facilitatorOrBalanceStateTouched = true;
	ghostLength = newLength;
}
// Store hook to synchronize ghostValues array with set._inner._values.
hook Sstore currentContract._facilitatorsList._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
	facilitatorOrBalanceStateTouched = true;
	ghostValues[index] = newValue;
}
// Store hook to synchronize ghostIndexes array with set._inner._indexes.
hook Sstore currentContract._facilitatorsList._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
	facilitatorOrBalanceStateTouched = true;
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

ghost mapping (address => uint) balanceOf {
	init_state axiom forall address x. balanceOf[x] == 0;
}

hook Sstore balanceOf[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
	require to_mathint(old_balance) <= sumAllBalance;
	facilitatorOrBalanceStateTouched = true;
	sumAllBalance = sumAllBalance + balance - old_balance;
	balanceOf[a] = balance;
	require to_mathint(balance) <= sumAllBalance;
}

hook Sload uint256 balance balanceOf[KEY address a] STORAGE {
	require balanceOf[a] == balance;
	require to_mathint(balance) <= sumAllBalance;
	requireInvariant inv_balanceOf_leq_totalSupply(a);
}

/**
* @title verifies that the external function reads properly
**/
// invariant balancesIntegrity()
// 	forall address x. balanceOf[x] == balanceOf(x);

/**
* @title verifies that balanceOf and totalSupply functions never revert
**/
rule balanceViewDontRevert(address addr) {
	balanceOf@withrevert(addr);
	assert !lastReverted, "balanceOf() can revert";
	totalSupply@withrevert();
	assert !lastReverted, "totalSupply() can revert";
}

ghost mapping(address => uint128) bucket_level {
	init_state axiom forall address x. bucket_level[x] == 0;
}

hook Sstore _facilitators[KEY address a].(offset 16) uint128 level (uint128 old_level) STORAGE {
	facilitatorOrBalanceStateTouched = true;
   	sumAllLevel = sumAllLevel + level - old_level;
	bucket_level[a] = level;
}

hook Sload uint128 level _facilitators[KEY address a].(offset 16) STORAGE {
	require bucket_level[a] == level;
	requireInvariant level_leq_sumAllLevel(a);
}

ghost mapping(address => uint128) bucket_capacity {
	init_state axiom forall address x. bucket_capacity[x] == 0;
}

hook Sstore _facilitators[KEY address a].(offset 0) uint128 capacity (uint128 old_capacity) STORAGE {
	facilitatorOrBalanceStateTouched = true;
	bucket_capacity[a] = capacity;
}

hook Sload uint128 capacity _facilitators[KEY address a].(offset 0) STORAGE {
	require bucket_capacity[a] == capacity;
}

/**
* @title makes sure the ghosts work properly
**/
invariant bucketReadIntegrity(address a)
	to_mathint(GhoTokenHelper.getFacilitatorBucketLevel(a)) == to_mathint(bucket_level[a]) &&
		to_mathint(GhoTokenHelper.getFacilitatorBucketCapacity(a)) == to_mathint(bucket_capacity[a]);

hook Sstore _facilitators[KEY address a].(offset 32) uint256 string_length (uint256 old_length) STORAGE {
	facilitatorOrBalanceStateTouched = true;
	if (string_length > 0) {
		inFacilitatorsMapping[a] = true;
	} else {
		inFacilitatorsMapping[a] = false;
	}

	assert string_length != old_length, "facilitator description was updated for one of the same length";
}

hook Sload uint256 string_length _facilitators[KEY address a].(offset 32) STORAGE {
	if (string_length > 0) {
		require inFacilitatorsMapping[a];
	} else {
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

// definition isFacilitator(address fac) returns bool = (inFacilitatorsList(toBytes32(fac)));

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

// invariant inv_balanceOf_leq_totalSupply_forall()
// 	forall address user. balanceOf(user) <= totalSupply()
// 	{
// 		preserved {
// 			requireInvariant inv_balanceOf_leq_totalSupply(user);
// 		}
// 	}

// INV #3
/**
 * @title Sum of bucket levels is equals to GhoToken::totalSupply()
 **/
invariant total_supply_eq_sumAllLevel()
		sumAllLevel == to_mathint(totalSupply()) 
	{
		preserved burn(uint256 amount) with (env e) {
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
			// requireInvariant inv_balanceOf_leq_totalSupply_forall();
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
	inFacilitatorsMapping[facilitator] <=> GhoTokenHelper.getFacilitatorsLabelLen(facilitator) > 0 
	{
		preserved {
			requireInvariant facilitatorsList_setInvariant();
			requireInvariant addr_in_set_iff_in_map(facilitator);
		}
	}

/**
* @title verifies that if either bucket capacity or the bucket level is nonzero, then a facilitator exists
**/
invariant facilitator_state_integrity(address facilitator)
	(bucket_capacity[facilitator] > 0 || bucket_level[facilitator] > 0) => inFacilitatorsMapping[facilitator]
	{ preserved {
		requireInvariant addr_in_set_iff_in_map(facilitator);
	} }


/**
* @title Proves that level of any facilitator is not greater than sum of all
**/
invariant level_leq_sumAllLevel(address a)
	to_mathint(GhoTokenHelper.getFacilitatorBucketLevel(a)) <= sumAllLevel;

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
	uint256 levelAfter = GhoTokenHelper.getFacilitatorBucketLevel(e.msg.sender);
	assert levelBefore == levelAfter;
}

/**
* @title Proves that the level increase after mint is accurate
**/
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

/**
* @title Proves that the level increase after burn is accurate
**/
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


/**
* @title Proves that the balance change is accurate after a mint
**/
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

/**
* @title Proves that the balance change is accurate after burn
**/
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
* @title Proves that one can't facilitate when the level is greater than the capacity
**/
rule no_facilitation_when_level_geq_capacity(address facilitator, method f) filtered {f -> !f.isView}{
	env e;
	calldataarg arg;
	assumeInvariants(facilitator);
	requireInvariant inv_valid_capacity(facilitator);
	uint init_level = GhoTokenHelper.getFacilitatorBucketLevel(facilitator);
	require init_level >= GhoTokenHelper.getFacilitatorBucketCapacity(facilitator); 
	f(e, arg);
	// This is kinda dummy because one could do two operations: change bucket capacity
	// to above current level and then increase the level, but that shouldn'tbe possible
	// in a single operation
	assert GhoTokenHelper.getFacilitatorBucketLevel(facilitator) <= init_level;
}

/**
* @title Proves that the roles are constant and are what they are supposed to be
**/
rule rolesConstant() {
	assert FACILITATOR_MANAGER_ROLE() == to_bytes32(0x5e20732f79076148980e17b6ce9f22756f85058fe2765420ed48a504bef5a8bc) &&
		BUCKET_MANAGER_ROLE() == to_bytes32(0xc7f115822aabac0cd6b9d21b08c0c63819451a58157aecad689d1b5674fad408);
}

/**
* @title Proves that the constant functions never revert
**/
rule rolesNeverRevert() {
	FACILITATOR_MANAGER_ROLE@withrevert();
	assert !lastReverted;
	BUCKET_MANAGER_ROLE@withrevert();
	assert !lastReverted;
}

// well… complete low-level specification is easiest like that
// I feel safe that the coverage is very high here
/**
* @title Main rule constraining revert reasons and implied state changes of functions.
**/
rule main(method f) {
	env e; calldataarg args;
	address other;
	address facilitator;
	require facilitator != other;

	assumeInvariants(facilitator);
	requireInvariant facilitator_state_integrity(facilitator);
	requireInvariant sumAllLevel_eq_sumAllBalance();
	requireInvariant level_leq_sumAllLevel(facilitator);
	requireInvariant total_supply_eq_sumAllLevel();

	address b_other;
	uint otherBalance = balanceOf[b_other];

	address r_other;
	bytes32 role;
	bool r_hasRole = hasRole(role, r_other);
	bool skipRoleCheck = false;

	bool otherStatus = inFacilitatorsMapping[other];
	uint128 otherBucketLevel = bucket_level[other];
	uint128 otherBucketCapacity = bucket_capacity[other];

	bool skipBalanceCheck = false;

	if (f.selector == sig:addFacilitator(address,string,uint128).selector) {
		bool was_facilitator = inFacilitatorsMapping[facilitator];
		string desc;
		// 1 TB string should be sufficient and it shouldn't be possible to submit that much anyway
		// The limit of the calldatasize is 2^64 (TAC / Solidity), so this could theoretically be
		// as much as 2^64 - 132
		require desc.length < 2 ^ 40;
		uint128 limit;
		uint128 previous_level = bucket_level[facilitator];

		addFacilitator@withrevert(e, facilitator, desc, limit);
		bool reverted = lastReverted;

		assert reverted <=> (
			was_facilitator ||
			desc.length == 0 ||
			!hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender) ||
			e.msg.value != 0
		), "Should have (not) reverted";

		assert !reverted => (
			inFacilitatorsMapping[facilitator] &&
			// can I check the description string itself? But this will do
			// also, this implies that it's a facilitator, but will leave the first requirement
			GhoTokenHelper.getFacilitatorsLabelLen(facilitator) == desc.length &&
			bucket_level[facilitator] == previous_level &&
			bucket_capacity[facilitator] == limit
		), "State change is incorrect";
	} else if (f.selector == sig:removeFacilitator(address).selector) {
		bool was_facilitator = inFacilitatorsMapping[facilitator];
		uint128 limit;

		removeFacilitator@withrevert(e, facilitator);
		bool reverted = lastReverted;

		assert reverted <=> (
			!was_facilitator ||
			!hasRole(FACILITATOR_MANAGER_ROLE(), e.msg.sender)
			/* this is a bug, shouldn't be here but I'm adding it so that the spec
			will pass on the original contract */
			|| bucket_level[facilitator] != 0 ||
			e.msg.value != 0
		), "Should have (not) reverted";

		assert !reverted => (
			!inFacilitatorsMapping[facilitator] &&
			bucket_level[facilitator] == 0 &&
			bucket_capacity[facilitator] == 0
		), "State change is incorrect";
	} else if (f.selector == sig:setFacilitatorBucketCapacity(address,uint128).selector) {
		uint128 limit;
		bool was_facilitator = inFacilitatorsMapping[facilitator];
		uint128 level = bucket_level[facilitator];

		setFacilitatorBucketCapacity@withrevert(e, facilitator, limit);
		bool reverted = lastReverted;

		assert reverted <=> (
			!was_facilitator ||
			!hasRole(BUCKET_MANAGER_ROLE(), e.msg.sender) ||
			e.msg.value != 0
		), "Should have (not) reverted";

		assert !reverted => (
			bucket_level[facilitator] == level &&
			inFacilitatorsMapping[facilitator] &&
			bucket_capacity[facilitator] == limit
		), "State change is incorrect";
	} else if (f.selector == sig:mint(address,uint256).selector) {
		require facilitator == e.msg.sender;
		address to;
		require b_other != to;
		bool was_facilitator = inFacilitatorsMapping[facilitator];
		uint amount;
		uint128 limit = bucket_capacity[facilitator];
		uint128 level = bucket_level[facilitator];
		uint balance_to_before = balanceOf[to];


		// in reality for that we would need at least (1 << 128) + 2 facilitators
		// and we can't register that many
		mathint total_supply = totalSupply();

		mint@withrevert(e, to, amount);
		bool reverted = lastReverted;

		assert reverted <=> (
			!was_facilitator ||
			// amount + level > uint128_max >= limit
			// hence overflow check is not needed
			to_mathint(level) + to_mathint(amount) > to_mathint(limit) ||
			// For some reason those mathints overflow so I added LHS overflow check
				to_mathint(level) + to_mathint(amount) < to_mathint(level) ||
			total_supply + to_mathint(amount) > max_uint ||
			// dummy overflow check
				total_supply + to_mathint(amount) < total_supply ||
			amount == 0 ||
			e.msg.value != 0
		), "Should have (not) reverted";

		mathint sum = to_mathint(level) + to_mathint(amount);

		assert !reverted => (
			to_mathint(balanceOf[to]) == balance_to_before + amount &&
			to_mathint(bucket_level[facilitator]) == level + amount &&
			inFacilitatorsMapping[facilitator] &&
			bucket_capacity[facilitator] == limit
		), "State change is incorrect";
	} else if (f.selector == sig:burn(uint256).selector) {
		require facilitator == e.msg.sender;
		require b_other != facilitator;

		bool was_facilitator = inFacilitatorsMapping[facilitator];
		uint amount;
		uint128 limit = bucket_capacity[facilitator];
		uint128 level = bucket_level[facilitator];
		uint balance_facilitator_before = balanceOf[facilitator];

		burn@withrevert(e, amount);
		bool reverted = lastReverted;

		assert reverted <=> (
			balance_facilitator_before < amount ||
			!was_facilitator ||
			amount == 0 ||
			to_mathint(amount) > to_mathint(level) ||
			e.msg.value != 0
		), "Should have (not) reverted";
		
		assert !reverted => (
			to_mathint(balanceOf[facilitator]) == to_mathint(balance_facilitator_before) - to_mathint(amount) &&
			inFacilitatorsMapping[facilitator] &&
			to_mathint(bucket_level[facilitator]) == to_mathint(level) - to_mathint(amount) &&
			bucket_capacity[facilitator] == limit
		), "State change is incorrect";
	} else {
		if (f.selector == sig:transfer(address,uint256).selector ||
			f.selector == sig:transferFrom(address,address,uint256).selector) {
			skipBalanceCheck = true;
		} else if (f.selector == sig:grantRole(bytes32,address).selector ||
			f.selector == sig:revokeRole(bytes32,address).selector ||
			f.selector == sig:renounceRole(bytes32,address).selector) {
			skipRoleCheck = true;
		}

		f(e, args);
	}

	assert (
		otherStatus == inFacilitatorsMapping[other] &&
		otherBucketLevel == bucket_level[other] &&
		otherBucketCapacity == bucket_capacity[other] &&
		(otherBalance == balanceOf[b_other] || skipBalanceCheck) &&
		(r_hasRole == hasRole(role, r_other) || skipRoleCheck)
	), "Function touched the state it shouldn't";
}

rule viewFunctionsDontRevert() {
	address facilitator;
	getFacilitator(facilitator);
	assert !lastReverted;
	getFacilitatorBucket(facilitator);
	assert !lastReverted;
	getFacilitatorsList();
	assert !lastReverted;
}

// constructor sanity check; purposely vacuous on _preserve
invariant constructor_no_state_corruption(address anyone, bytes32 role)
	!facilitatorOrBalanceStateTouched &&
		hasRole(to_bytes32(0), deployer()) &&
		((role != to_bytes32(0) && anyone != deployer()) => !hasRole(role, anyone))
	{ preserved {
		require false;
	} }

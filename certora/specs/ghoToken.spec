
/**
@notice set_facilitatorList contains 
ghost, hooks and invariant of the valid state of _facilitatorsList base on enumberableSet spec https://github.com/Certora/Examples/tree/master/CVLByExample/QuantifierExamples
**/
import "set_facilitatorList.spec";

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
	function GhoTokenHelper.getFacilitatorsLableLen(address facilitator) external  returns (uint256) envfree;
	function GhoTokenHelper.toBytes32(address) external returns (bytes32) envfree;
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
//
// Invariants
//

// INV #1
/**
* @title Length of AddressSet is less than 2^160
* @dev the assumption is safe because there are at most 2^160 unique addresses
* @dev the proof of the assumption is vacuous because length > loop_iter
*/
/*
invariant length_leq_max_uint160()
	getFacilitatorsListLen() < TWO_TO_160();
*/
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

// INV #8
/**
* @title AddressSet internal coherency
* @dev A facilitator address exists in AddressSet list (GhoToken._facilitatorsList._values)
* @dev if and only if it exists in AddressSet mapping (GhoToken._facilitatorsList._indexes)
*/

use invariant facilitatorsList_setInvariant;

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
		preserved addFacilitator(address f,string s,uint128 c) with (env e) {
			/* Due to an over approximation in the Prover,when assiging a new length to a string we consider that it is zero. Once https://certora.atlassian.net/browse/CERT-3500 is fixed remove */
			require(false);
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

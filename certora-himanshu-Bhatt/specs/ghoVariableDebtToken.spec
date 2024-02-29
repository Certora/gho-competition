import "VariableDebtToken.spec";

using GhoDiscountRateStrategy as discStrategy;
using DummyERC20WithTimedBalanceOf as discountToken;
using DummyPool as pool;

methods{
	
  	/***********************************;
    *    PoolAddressesProvider.sol     *;
    ************************************/
	function _.getACLManager() external => CONSTANT;

	/************************;
    *    ACLManager.sol     *;
    *************************/
	function _.isPoolAdmin(address) external => CONSTANT;

	/******************************************************************;
	*	DummyERC20WithTimedBalanceOf.sol (linked to _discountToken)   *;
	*******************************************************************/
	// represent a random balance per block 
	function discountToken.balanceOf(address user) external returns (uint256) with (env e) => balanceOfDiscountTokenAtTimestamp(user, e.block.timestamp) ;

  	/************************************;
    *   DummyPool.sol (linked to POOL)  *;
    *************************************/
	// represent a random index per block
	function pool.getReserveNormalizedVariableDebt(address asset) external returns (uint256) with (env e) => indexAtTimestamp(e.block.timestamp);

	/************************************;
	*	GhoVariableDebtTokenHarness.sol	*;
	*************************************/
	function discStrategy.calculateDiscountRate(uint256, uint256) external returns (uint256) envfree;

	/************************************;
	*	GhoVariableDebtTokenHarness.sol	*;
	*************************************/
	function getUserCurrentIndex(address) external returns (uint256) envfree;
	function getUserDiscountRate(address) external returns (uint256) envfree;
	function getUserAccumulatedDebtInterest(address) external returns (uint256) envfree;
	function getBalanceOfDiscountToken(address) external returns (uint256);

	/********************************;
	*	GhoVariableDebtToken.sol	*;
	*********************************/
	function totalSupply() external returns(uint256) envfree;
	function balanceOf(address) external returns (uint256);
	function mint(address, address, uint256, uint256) external returns (bool, uint256);
	function burn(address ,uint256 ,uint256) external returns (uint256);
	function scaledBalanceOf(address) external returns (uint256) envfree;
	function getBalanceFromInterest(address) external returns (uint256) envfree;
	function rebalanceUserDiscountPercent(address) external;
	function updateDiscountDistribution(address ,address ,uint256 ,uint256 ,uint256) external;
}

/**
* CVL implementation of rayMul
**/
function rayMulCVL(uint256 a, uint256 b) returns mathint {
	return ((a * b + (ray() / 2)) / ray());
}
function rayDivCVL(uint256 a, uint256 b) returns mathint {
	return ((a * ray() + (b / 2)) / b);
}


//todo: check balanceof after mint (stable index), burn after balanceof

definition MAX_DISCOUNT() returns uint256 = 10000; // equals to 100% discount, in points

ghost mapping(address => mapping (uint256 => uint256)) discount_ghost;
ghost mapping(uint256 => uint256) index_ghost;

/**
* Query index_ghost for the index value at the input timestamp
**/
function indexAtTimestamp(uint256 timestamp) returns uint256 {
    require index_ghost[timestamp] >= ray();
    return index_ghost[timestamp];
    // return 1001684385021630839436707910;//index_ghost[timestamp];
}

/**
* Query discount_ghost for the [user]'s balance of discount token at [timestamp]
**/
function balanceOfDiscountTokenAtTimestamp(address user, uint256 timestamp) returns uint256 {
	return discount_ghost[user][timestamp];
}

/**
* Returns an env instance with [ts] as the block timestamp
**/
function envAtTimestamp(uint256 ts) returns env {
	env e;
	require(e.block.timestamp == ts);
	return e;
}

/**
* @title at any point in time, the user's discount rate isn't larger than 100%
**/
invariant discountCantExceed100Percent(address user)
	getUserDiscountRate(user) <= MAX_DISCOUNT()
	{
		preserved updateDiscountDistribution(address sender,address recipient,uint256 senderDiscountTokenBalance,uint256 recipientDiscountTokenBalance,uint256 amount) with (env e) {
			require(indexAtTimestamp(e.block.timestamp) >= ray());
		}
	}

/**
* Imported rules from VariableDebtToken.spec
**/
//pass
use rule disallowedFunctionalities;


/**
* @title proves that the user's balance of debt token (as reported by GhoVariableDebtToken::balanceOf) can't increase by calling any external non-mint function.
**/
//pass
rule nonMintFunctionCantIncreaseBalance(method f) filtered { f-> f.selector != sig:mint(address, address, uint256, uint256).selector } {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	// Forcing the index to be fixed (otherwise the rule times out). For non-fixed index replace `==` with `>=`
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) == indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);

	env e = envAtTimestamp(ts2);
	uint256 balanceBeforeOp = balanceOf(e, user);
	calldataarg args;
	f(e,args);
	mathint balanceAfterOp = balanceOf(e, user);
	mathint allowedDiff = indexAtTimestamp(ts2) / ray();
	// assert(balanceAfterOp != balanceBeforeOp + allowedDiff + 1);
	assert(balanceAfterOp <= balanceBeforeOp + allowedDiff);
}

/**
* @title proves that a call to a non-mint operation won't increase the user's balance of the actual debt tokens (i.e. it's scaled balance)
**/
// pass
rule nonMintFunctionCantIncreaseScaledBalance(method f) filtered { f-> f.selector != sig:mint(address, address, uint256, uint256).selector } {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = scaledBalanceOf(user);
	env e = envAtTimestamp(ts2);
	calldataarg args;
	f(e,args);
	uint256 balanceAfterOp = scaledBalanceOf(user);
	assert(balanceAfterOp <= balanceBeforeOp);
}

/**
* @title proves that debt tokens aren't transferable
**/
// pass
rule debtTokenIsNotTransferable(method f) {
	address user1;
	address user2;
	require(user1 != user2);
	uint256 scaledBalanceBefore1 = scaledBalanceOf(user1);
	uint256 scaledBalanceBefore2 = scaledBalanceOf(user2);
	env e;
	calldataarg args;
	f(e,args);
	uint256 scaledBalanceAfter1 = scaledBalanceOf(user1);
	uint256 scaledBalanceAfter2 = scaledBalanceOf(user2);

	assert( scaledBalanceBefore1 + scaledBalanceBefore2 == scaledBalanceAfter1 + scaledBalanceAfter2 
	=> (scaledBalanceBefore1 == scaledBalanceAfter1 && scaledBalanceBefore2 == scaledBalanceAfter2));
}

/**
* @title proves that only burn/mint/rebalanceUserDiscountPercent/updateDiscountDistribution can modify user's scaled balance
**/
// pass
rule onlyCertainFunctionsCanModifyScaledBalance(method f) {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = scaledBalanceOf(user);
	env e = envAtTimestamp(ts2);
	calldataarg args;
	f(e,args);
	uint256 balanceAfterOp = scaledBalanceOf(user);
	assert(balanceAfterOp != balanceBeforeOp => (
		(f.selector == sig:mint(address ,address ,uint256 ,uint256).selector) ||
		(f.selector == sig:burn(address ,uint256 ,uint256).selector) ||
		(f.selector == sig:updateDiscountDistribution(address ,address ,uint256 ,uint256 ,uint256).selector) ||
		(f.selector == sig:rebalanceUserDiscountPercent(address).selector)));
}

/**
* @title proves that only a call to decreaseBalanceFromInterest will decrease the user's accumulated interest listing.
**/
// pass
rule userAccumulatedDebtInterestWontDecrease(method f) {
	address user;
	uint256 ts1;
	uint256 ts2;
	require(ts2 >= ts1);
	require((indexAtTimestamp(ts1) >= ray()) && 
			(indexAtTimestamp(ts2) >= indexAtTimestamp(ts1)));

	require(getUserCurrentIndex(user) == indexAtTimestamp(ts1));
	requireInvariant discountCantExceed100Percent(user);
	uint256 initAccumulatedInterest = getUserAccumulatedDebtInterest(user);
	env e2 = envAtTimestamp(ts2);
	calldataarg args;
	f(e2,args);
	uint256 finAccumulatedInterest = getUserAccumulatedDebtInterest(user);
	assert(initAccumulatedInterest > finAccumulatedInterest => f.selector == sig:decreaseBalanceFromInterest(address, uint256).selector);
}

/**
* @title proves that a user can't nullify its debt without calling burn
**/
// pass
rule userCantNullifyItsDebt(method f) {
    address user;
    env e;
    env e2;
	require(getUserCurrentIndex(user) == indexAtTimestamp(e.block.timestamp));
	requireInvariant discountCantExceed100Percent(user);
	uint256 balanceBeforeOp = balanceOf(e, user);
	calldataarg args;
    require e2.block.timestamp == e.block.timestamp;
	f(e2,args);
	uint256 balanceAfterOp = balanceOf(e, user);
	assert((balanceBeforeOp > 0 && balanceAfterOp == 0) => (f.selector == sig:burn(address, uint256, uint256).selector));
}

/***************************************************************
* Integrity of Mint
***************************************************************/

/**
* @title proves that after calling mint, the user's discount rate is up to date
**/
rule integrityOfMint_updateDiscountRate() {
	address user1;
	address user2;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	mint(e, user1, user2, amount, index);
	uint256 debtBalance = balanceOf(e, user2);
	uint256 discountBalance = getBalanceOfDiscountToken(e, user2);
	uint256 discountRate = getUserDiscountRate(user2);
	assert(discStrategy.calculateDiscountRate(debtBalance, discountBalance) == discountRate);
}

/**
* @title proves the after calling mint, the user's state is updated with the recent index value
**/
rule integrityOfMint_updateIndex() {
	address user1;
	address user2;
	env e;
	uint256 amount;
	uint256 index;
	mint(e, user1, user2, amount, index);
	assert(getUserCurrentIndex(user2) == index);
}

/**
* @title proves that on a fixed index calling mint(user, amount) will increase the user's scaled balance by amount. 
**/
// pass
rule integrityOfMint_updateScaledBalance_fixedIndex() {
	address user;
	env e;
	uint256 balanceBefore = balanceOf(e, user);
	uint256 scaledBalanceBefore = scaledBalanceOf(user);
	address caller;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	require(getUserCurrentIndex(user) == index);
	uint256 _rate=getUserDiscountRate(user);

	mint(e, caller, user, amount, index);

	uint256 rate_=getUserDiscountRate(user);
	uint256 balanceAfter = balanceOf(e, user);
	mathint scaledBalanceAfter = scaledBalanceOf(user);
	mathint scaledAmount = rayDivCVL(amount, index);

	assert(scaledBalanceAfter == scaledBalanceBefore + scaledAmount);
	assert rate_<=_rate;
}

// if disountScled is greater than amountScaled , burn happens
// https://prover.certora.com/output/42902/7aad011a20534ab2b63b7fbfb701c870/?anonymousKey=e82ec7ca0ab45dcd02ebc636d9cb0e9b2d8cfd5e
rule integrityOfMint_updateScaledBalance_fixedIndex_2() {
	address user;
	env e;
	uint256 balanceBefore = balanceOf(e, user);
	uint256 scaledBalanceBefore = scaledBalanceOf(user);
	address caller;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	uint256 discountPercent=getUserDiscountRate(user);
	require(getUserCurrentIndex(user) == assert_uint256(2*ray()) && index == assert_uint256(4*ray()));
	
	uint256 balanceIncrease;mathint discountScaled;
	balanceIncrease,discountScaled=getDiscountScaled(e,user,scaledBalanceBefore,discountPercent,index);

	mint(e, caller, user, amount, index);

	uint256 balanceAfter = balanceOf(e, user);
	uint256 scaledBalanceAfter = scaledBalanceOf(user);
	mathint scaledAmount = rayDivCVL(amount, index);

	// assert scaledBalanceAfter < scaledBalanceBefore => discountScaled > scaledAmount;
	assert scaledBalanceAfter < scaledBalanceBefore <=> discountScaled > scaledAmount;
	assert scaledBalanceAfter > scaledBalanceBefore <=> scaledAmount > discountScaled;
	assert scaledBalanceAfter < scaledBalanceBefore => scaledBalanceBefore==assert_uint256(scaledBalanceAfter + assert_uint256(discountScaled-scaledAmount));
	assert scaledBalanceAfter > scaledBalanceBefore => scaledBalanceAfter== assert_uint256(scaledBalanceBefore + assert_uint256(scaledAmount-discountScaled));
}


// https://prover.certora.com/output/42902/11598f7825cb4a48b896b55ff3c4c2e4/?anonymousKey=ac3cca5fc6c016997e6f5fe6b7a0d79ae1d05393
rule if_discount_discountPecentNotZero(method f,env e,calldataarg args)filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;
	require(balanceOf(e,user) < rayMul(e,scaledBalanceOf(user),indexAtTimestamp(e.block.timestamp))=>getUserDiscountRate(user) >0);
	f(e,args);
	assert balanceOf(e,user) < rayMul(e,scaledBalanceOf(user),indexAtTimestamp(e.block.timestamp))=>getUserDiscountRate(user) >0;
}



// if scaled balance is increased than net balance (balanceOf()) is also increased
// https://prover.certora.com/output/42902/07b3d3a884d642c8b4c2802efe0fec91/?anonymousKey=212003f83545c348e122559f5ede1e12fc7b2695
rule prop1(method f,env e,calldataarg args) filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;
	uint256 _scaled=scaledBalanceOf(user);
	uint256 _balance=balanceOf(e,user);
	uint256 _index=getUserCurrentIndex(user);
	uint256 _discountRate=getUserDiscountRate(user);
	require(indexAtTimestamp(e.block.timestamp)>=ray() && _index<=indexAtTimestamp(e.block.timestamp));
	f(e,args);
	uint256 scaled_=scaledBalanceOf(user);       
	uint256 balance_=balanceOf(e,user);
	uint256 index_=getUserCurrentIndex(user);
	uint256 discountRate_=getUserDiscountRate(user);

	assert _scaled < scaled_ => _balance < balance_;

}


/** 1_2. if a user actual balance is less than his balance_without_discount than user's discount percent mut be greater than 0 and index must be less than current index of the pool.
@LINK:- https://prover.certora.com/output/42902/e337fea761634a7cb80be164c29bf577/?anonymousKey=beed0cf881f03cdf6f31d40bdc6ee407bdc2a6d2
*/
rule prop1_2(method f,env e,calldataarg args) filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;

	mathint _balance=balanceOf(e,user);
	mathint _balance_without_discount= rayMul(e,scaledBalanceOf(user),indexAtTimestamp(e.block.timestamp));
	mathint _discountRate=getUserDiscountRate(user);
	mathint _userCurrentIndex=getUserCurrentIndex(user);
	mathint _currentIndex=indexAtTimestamp(e.block.timestamp);

	// require(getUserCurrentIndex(user) ==assert_uint256(ray()) && indexAtTimestamp(e.block.timestamp)==assert_uint256(ray()+5));
	// require()
	require _balance < _balance_without_discount => _discountRate >0 && _userCurrentIndex < _currentIndex;

	f(e,args);
	
	mathint balance=balanceOf(e,user);
	mathint balance_without_discount= rayMul(e,scaledBalanceOf(user),indexAtTimestamp(e.block.timestamp));
	mathint discountRate=getUserDiscountRate(user);
	mathint userCurrentIndex=getUserCurrentIndex(user);
	mathint currentIndex=indexAtTimestamp(e.block.timestamp);

	assert (balance < balance_without_discount =>discountRate >0 && userCurrentIndex < currentIndex);
}


// https://prover.certora.com/output/42902/1d79ded4d5d14d88868d7207dcb47086/?anonymousKey=4781cc8d4d07975cf88682faa125a716a723615c

rule balanceOf_lessThanEqual_scaledBalance_X_index(method f,calldataarg args,env e)filtered{f->!f.isView && !disAllowedFunctions(f)} {
	address user;
	uint256 index=indexAtTimestamp(e.block.timestamp);
	require( balanceOf(e,user)<=rayMul(e,scaledBalanceOf(user),index));
	f(e,args);
	assert balanceOf(e,user)<=rayMul(e,scaledBalanceOf(user),index);
}

// if user has zero discount his balanceOf() must be equal to rayMul(scaledBalanceOf(user,index))
// https://prover.certora.com/output/42902/5043cd6e7329411886e36adfbc473d5a/?anonymousKey=4efb9409c4a19a89b4fb2bf5c29ead47c8b6172a
rule no_discount_balance(){
	address user;env e;
	require(getUserDiscountRate(user)==0);
	assert balanceOf(e,user)==rayMul(e,scaledBalanceOf(user),indexAtTimestamp(e.block.timestamp));
}

// https://prover.certora.com/output/42902/31d76f582db148c08fb78bf448f4fbb9/?anonymousKey=511029af82e3361a1c8959d40502bbb96d2296d4
rule less_debtBalance_more_discountRate(env e,method f,calldataarg args) filtered{f->!disAllowedFunctions(f)} {
	uint256 a;uint256 b;
	require(a<b);
	uint256 x;
	require  discStrategy.calculateDiscountRate(a,x)>discStrategy.calculateDiscountRate(b,x);

	f(e,args);

	assert  discStrategy.calculateDiscountRate(a,x)>discStrategy.calculateDiscountRate(b,x);
}

/**
* @title proves that mint can't effect other user's scaled balance
**/
// pass
rule integrityOfMint_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 index;
	address targetUser;
	address caller;
	mint(e, caller, targetUser, amount, index);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}

/**
* @title proves that when calling mint, the user's balance (as reported by GhoVariableDebtToken::balanceOf) will increase if the call is made on bahalf of the user.
**/
rule onlyMintForUserCanIncreaseUsersBalance() {
	address user1;
    env e;
	require(getUserCurrentIndex(user1) == indexAtTimestamp(e.block.timestamp));
	
	uint256 finBalanceBeforeMint = balanceOf(e, user1);
	uint256 amount;
	mint(e,user1, user1, amount, indexAtTimestamp(e.block.timestamp));
	uint256 finBalanceAfterMint = balanceOf(e, user1);

	// assert(finBalanceAfterMint != finBalanceBeforeMint);
	assert(finBalanceAfterMint > finBalanceBeforeMint);
}

//pass
use rule integrityMint_atoken;

/***************************************************************
* Integrity of Burn
***************************************************************/

/**
* @title proves that after calling burn, the user's discount rate is up to date
**/
rule integrityOfBurn_updateDiscountRate() {
	address user;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	burn(e, user, amount, index);
	uint256 debtBalance = balanceOf(e, user);
	uint256 discountBalance = getBalanceOfDiscountToken(e, user);
	uint256 discountRate = getUserDiscountRate(user);
	assert(discStrategy.calculateDiscountRate(debtBalance, discountBalance) == discountRate);
}

/**
* @title proves the after calling burn, the user's state is updated with the recent index value
**/
rule integrityOfBurn_updateIndex() {
	address user;
	env e;
	uint256 amount;
	uint256 index;
	burn(e, user, amount, index);
	assert(getUserCurrentIndex(user) == index);
}

/**
* @title proves that calling burn with 0 amount doesn't change the user's balance
**/
use rule burnZeroDoesntChangeBalance;

/**
* @title proves a concrete case of repaying the full debt that ends with a zero balance
**/
rule integrityOfBurn_fullRepay_concrete() {
	env e;
	address user;
	uint256 currentDebt = balanceOf(e, user);
	uint256 index = indexAtTimestamp(e.block.timestamp);
	// handle timeouts
	require(getUserCurrentIndex(user) == ray());
	require(to_mathint(index) == 2*ray());
	require(to_mathint(scaledBalanceOf(user)) == 4*ray());
	
	burn(e, user, currentDebt, index);
	uint256 scaled = scaledBalanceOf(user);
	assert(scaled == 0);
}


/**
* @title proves that burn can't effect other user's scaled balance
**/
// pass
rule integrityOfBurn_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 index;
	address targetUser;
	burn(e,targetUser, amount, index);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}


/***************************************************************
* Integrity of rebalanceUserDiscountPercent
***************************************************************/

/**
* @title proves that after calling rebalanceUserDiscountPercent, the user's discount rate is up to date
**/
rule integrityOfRebalanceUserDiscountPercent_updateDiscountRate() {
	address user;
	env e;
	rebalanceUserDiscountPercent(e, user);
	assert(discStrategy.calculateDiscountRate(balanceOf(e, user), getBalanceOfDiscountToken(e, user)) == getUserDiscountRate(user));
}
rule integrityOfRebalanceUserDiscountPercent_decreaseScaledBalance() {
	address user;
	uint256 _s=scaledBalanceOf(user);
	env e;
	rebalanceUserDiscountPercent(e, user);
	assert(discStrategy.calculateDiscountRate(balanceOf(e, user), getBalanceOfDiscountToken(e, user)) == getUserDiscountRate(user));
	assert scaledBalanceOf(user) <= _s;
}

/**
* @title proves that after calling rebalanceUserDiscountPercent, the user's state is updated with the recent index value
**/
rule integrityOfRebalanceUserDiscountPercent_updateIndex() {
	address user;
	env e;
	rebalanceUserDiscountPercent(e, user);
	uint256 index = indexAtTimestamp(e.block.timestamp);
	assert(getUserCurrentIndex(user) == index);
}

/**
* @title proves that rebalanceUserDiscountPercent can't effect other user's scaled balance
**/
// pass
rule integrityOfRebalanceUserDiscountPercent_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	address targetUser;
	rebalanceUserDiscountPercent(e, targetUser);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => otherUser == targetUser);
}

/***************************************************************
* Integrity of balanceOf
***************************************************************/

/** 
@NOTE:-. Unit test of balanceOf

*/

rule prop2(method f,calldataarg args) filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;env e;

	uint256 _scaledBalance=scaledBalanceOf(user);
	uint256 _balance=balanceOf(e,user);
	uint256 _userCurrentIndex=getUserCurrentIndex(user);
	uint256  _index=indexAtTimestamp(e.block.timestamp);
	uint256 _discountPercent=getUserDiscountRate(user);

	require(_index ==assert_uint256(4*ray()) && _userCurrentIndex==assert_uint256(2*ray())  );

	uint256 _balanceInc=assert_uint256(rayMul(e,_scaledBalance,_index) -rayMul( e,_scaledBalance,_userCurrentIndex));

	uint256 __balance=assert_uint256(rayMul(e,_scaledBalance,_index) - percentMul_external(e, _balanceInc,_discountPercent));

	require(_balance==__balance);

	f(e,args);

	uint256 scaledBalance_=scaledBalanceOf(user);
	uint256 balance_=balanceOf(e,user);
	uint256 userCurrentIndex_=getUserCurrentIndex(user);
	uint256 index_=indexAtTimestamp(e.block.timestamp);
	uint256 discountPercent_=getUserDiscountRate(user);

	uint256 balanceInc_=assert_uint256(rayMul(e,scaledBalance_,index_) -rayMul(e, scaledBalance_,userCurrentIndex_));

	uint256 balance__=assert_uint256(rayMul(e,scaledBalance_,index_) - percentMul_external(e,balanceInc_,discountPercent_));

	// assert balance_==assert_uint256(balance__+1);
	assert balance_==balance__;
}




/**
* @title proves that a user with 100% discounts has a fixed balance over time
**/
rule integrityOfBalanceOf_fullDiscount() {
	address user;
	uint256 fullDiscountRate = 10000; //100%
	require(getUserDiscountRate(user) == fullDiscountRate);
	env e1;
	env e2;
	uint256 index1 = indexAtTimestamp(e1.block.timestamp);
	uint256 index2 = indexAtTimestamp(e2.block.timestamp);
	assert(balanceOf(e1, user) == balanceOf(e2, user));
}

/**
* @title proves that a user's balance, with no discount, is equal to rayMul(scaledBalance, current index)
**/
rule integrityOfBalanceOf_noDiscount() {
	address user;
	require(getUserDiscountRate(user) == 0);
	env e;
	uint256 scaledBalance = scaledBalanceOf(user);
	uint256 currentIndex = indexAtTimestamp(e.block.timestamp);
	mathint expectedBalance = rayMulCVL(scaledBalance, currentIndex);
	assert(to_mathint(balanceOf(e, user)) == expectedBalance);
}

/**
* @title proves the a user with zero scaled balance has a zero balance
**/
rule integrityOfBalanceOf_zeroScaledBalance() {
	address user;
	env e;
	uint256 scaledBalance = scaledBalanceOf(user);
	require(scaledBalance == 0);
	assert(balanceOf(e, user) == 0);
}

rule burnAllDebtReturnsZeroDebt(address user) {
    env e;
	uint256 _variableDebt = balanceOf(e, user);
	burn(e, user, _variableDebt, indexAtTimestamp(e.block.timestamp));
	uint256 variableDebt_ = balanceOf(e, user);
    assert(variableDebt_ == 0);
}

rule OnlyPoolCanChangeBalance(method f ,env e,calldataarg args) filtered{f -> !f.isView && !disAllowedFunctions(f)}{
	address user;
	uint256 _balance=balanceOf(e,user);
	uint256 _scaledBalance=scaledBalanceOf(user);
	f(e,args);
	uint256 balance_=balanceOf(e,user);
	uint256 scaledBalance_=scaledBalanceOf(user);
	// assert balance_!=_balance || scaledBalance_!=_scaledBalance => e.msg.sender==pool;
	// assert scaledBalance_!=_scaledBalance => e.msg.sender==pool;
	assert scaledBalance_>_scaledBalance => e.msg.sender==pool;
}

// https://prover.certora.com/output/42902/d5bb2149247a48a29d929c5797487d6a?anonymousKey=a65d56a059e7dea764d104d878b45ce769134d5b
rule allowance_decrease_correctly(env e){
	address user;address onBehalf;uint256 amount;uint256 index;
	require(user!=onBehalf);
	uint256 _allowance=borrowAllowance(e,onBehalf,user);

	mint(e,user,onBehalf,amount,index);

	uint256 allowance_=borrowAllowance(e,onBehalf,user);
	assert allowance_==assert_uint256(_allowance-amount);
}


/**
@NOTE:- if user's index is increades then his accumulated balance is increased correctly.
@LINK:- https://prover.certora.com/output/42902/827114ec257c478ab456fe8b064451c7/?anonymousKey=7674d341883f2e80c2f74234ad3bca6a2e9f7557
*/
rule prop3(method f,env e,calldataarg args)filtered{f->!f.isView && !disAllowedFunctions(f)} {
	address user;
	uint256 _userIndex=getUserCurrentIndex(user);
	uint256 scaledBalance=scaledBalanceOf(user);
	uint256 discountPercent=getUserDiscountRate(user);
	mathint _accumulated=getUserAccumulatedDebtInterest(user);

	f(e,args);

	uint256 userIndex_=getUserCurrentIndex(user);
	mathint accumulated_=getUserAccumulatedDebtInterest(user);
	uint256 balanceInc=getBalanceIncrease(e,scaledBalance,_userIndex,userIndex_);

	assert balanceInc>0 =>   accumulated_==_accumulated+(balanceInc-percentMul_external(e,balanceInc,discountPercent));
}

// if accumulated balance of user is increased his index must increase too.
// https://prover.certora.com/output/42902/603a90d59f2f4d50a376c8998128fb1e/?anonymousKey=5bbdc52fcc91384c286df778ec56b382b3f59b34
rule prop3_2(method f,env e,calldataarg args)filtered{f->!f.isView && !disAllowedFunctions(f)} {
	address user;
	uint256 _userIndex=getUserCurrentIndex(user);
	uint256 scaledBalance=scaledBalanceOf(user);
	uint256 discountPercent=getUserDiscountRate(user);
	mathint _accumulated=getUserAccumulatedDebtInterest(user);
	require(indexAtTimestamp(e.block.timestamp)>=ray());

	f(e,args);

	uint256 userIndex_=getUserCurrentIndex(user);
	mathint accumulated_=getUserAccumulatedDebtInterest(user);
	uint256 balanceInc=getBalanceIncrease(e,scaledBalance,_userIndex,userIndex_);

	assert accumulated_>_accumulated => userIndex_ > _userIndex;
}
// https://prover.certora.com/output/42902/e39840f9bb4d45f39123dca27ef52153/?anonymousKey=2f4f24ec38fa31b3cd20a891f3e47c3bd09452e9
rule only_ghoToken_decreases_accumulated(method f)filtered{f->!f.isView && !disAllowedFunctions(f)} {
	address user;
	mathint _accumulated=getUserAccumulatedDebtInterest(user);
	env e;calldataarg args;
	f(e,args);
	mathint accumulated_=getUserAccumulatedDebtInterest(user);
	assert accumulated_<_accumulated =>f.selector==sig:decreaseBalanceFromInterest(address,uint256).selector &&  e.msg.sender==getAToken(e);

}
// calling rebalanceUserDiscountPercent() twice is same as calling once
rule prop5(){
	address user;env e;
	rebalanceUserDiscountPercent(e,user);
	storage afterFirst=lastStorage;
	rebalanceUserDiscountPercent(e,user);
	storage afterSecond=lastStorage;

	assert afterFirst==afterSecond;
}


// if scaledBalance is decreased coz function other than burn() than user index is increased.
// https://prover.certora.com/output/42902/54177107c2e343908449cabde5c7b00e/?anonymousKey=29db7be276deb88534734abed8c2a454a51187f8
rule prop6(method f,env e,calldataarg args)filtered{f->!f.isView && !disAllowedFunctions(f)}{
	address user;
	uint256 _scaled=scaledBalanceOf(user);
	uint256 _index=getUserCurrentIndex(user);
	f(e,args);
	uint256 scaled_=scaledBalanceOf(user);
	uint256 index_=getUserCurrentIndex(user);
	assert scaled_ < _scaled && f.selector!=sig:burn(address,uint256,uint256).selector => index_>_index; 
}
// after calling updateDiscountDistribution balanceOf() of both sender and recipient is equal to their respective scaledbalanceOf().rayMul(indexAtTime(e.block.timestamp)).
//https://prover.certora.com/output/42902/07d4b8a7a9814df98d3c3d606fccbfdf/?anonymousKey=2baabc25c0efc46022fd4429b256460183dc2421
rule prop7(){
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 senderDiscountTokenBalance;
	uint256 recipientDiscountTokenBalance;
	address sender;
	address recipient;
	uint256 index=indexAtTimestamp(e.block.timestamp);
	uint256 _scaledBalanceBefore_sender = scaledBalanceOf(sender);
	uint256 _scaledBalanceBefore_recipient = scaledBalanceOf(recipient);

	uint256 balanceInc_sender;uint256 discountScaled_sender;
	balanceInc_sender,discountScaled_sender=getDiscountScaled(e,sender,_scaledBalanceBefore_sender,getUserDiscountRate(sender),index);
	uint256 balanceInc_recipient;uint256 discountScaled_recipient;
	balanceInc_recipient,discountScaled_recipient=getDiscountScaled(e,recipient,_scaledBalanceBefore_recipient,getUserDiscountRate(recipient),index);

	require(index==assert_uint256(4*ray()) && getUserCurrentIndex(sender)==assert_uint256(2*ray()) && getUserCurrentIndex(recipient)==(assert_uint256(3*ray())));

	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);

	uint256 scaledBalanceAfter_sender = scaledBalanceOf(sender);
	uint256 scaledBalanceAfter_recipient = scaledBalanceOf(recipient);

	uint256 balanceInc_sender_;uint256 discountScaled_sender_;
	balanceInc_sender_,discountScaled_sender_=getDiscountScaled(e,sender,scaledBalanceAfter_sender,getUserDiscountRate(sender),index);
	uint256 balanceInc_recipient_;uint256 discountScaled_recipient_;
	balanceInc_recipient_,discountScaled_recipient_=getDiscountScaled(e,recipient,scaledBalanceAfter_recipient,getUserDiscountRate(recipient),index);

	assert balanceOf(e,sender)==rayMul(e,scaledBalanceAfter_sender,index) && balanceOf(e,recipient)==rayMul(e,scaledBalanceAfter_recipient,index);
	assert _scaledBalanceBefore_sender>0 && _scaledBalanceBefore_recipient>0 => getUserCurrentIndex(sender)==index && getUserCurrentIndex(recipient)==index;
}


/**
* @title proves the after calling updateDiscountDistribution, the user's state is updated with the recent index value
**/
rule integrityOfUpdateDiscountDistribution_updateIndex() {
	address sender;
	address recipient;
	uint256 senderDiscountTokenBalance;
    uint256 recipientDiscountTokenBalance;
	env e;
	uint256 amount;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);
	assert(scaledBalanceOf(sender) > 0 => getUserCurrentIndex(sender) == index);
	assert(scaledBalanceOf(recipient) > 0 => getUserCurrentIndex(recipient) == index);
}


/**
* @title proves that updateDiscountDistribution can't effect other user's scaled balance
**/
// pass
rule integrityOfUpdateDiscountDistribution_userIsolation() {
	address otherUser;
	uint256 scaledBalanceBefore = scaledBalanceOf(otherUser);
	env e;
	uint256 amount;
	uint256 senderDiscountTokenBalance;
	uint256 recipientDiscountTokenBalance;
	address sender;
	address recipient;
	updateDiscountDistribution(e, sender, recipient, senderDiscountTokenBalance, recipientDiscountTokenBalance, amount);
	uint256 scaledBalanceAfter = scaledBalanceOf(otherUser);
	assert(scaledBalanceAfter != scaledBalanceBefore => (otherUser == sender || otherUser == recipient));
}


rule unit_updateDiscountDistribution(){
	address sender;address recipient;uint256 amount;env e;
	uint256 _scaledSender=scaledBalanceOf(sender);
	uint256 _scaledRecipient=scaledBalanceOf(recipient);
	uint256 _discountSenderRate=getUserDiscountRate(sender);
	uint256 _discountRecipientRate=getUserDiscountRate(recipient);
	uint256 _discountSenderBalance=getBalanceOfDiscountToken(e,sender);
	uint256 _discountRecipientBalance=getBalanceOfDiscountToken(e,recipient);

	uint256 a;uint256 discountScaledSender;uint256 discountScaledRecipient; uint256 index=indexAtTimestamp(e.block.timestamp); 
	a,discountScaledSender=getDiscountScaled(e,sender,_scaledSender,_discountSenderRate,index);
	a,discountScaledRecipient=getDiscountScaled(e,recipient,_scaledRecipient,_discountRecipientRate,index);
	require( _scaledSender >0 && _scaledRecipient>0 );
	require(index==assert_uint256(4*ray()) && getUserCurrentIndex(sender)==assert_uint256(2*ray()) && getUserCurrentIndex(recipient)==(assert_uint256(3*ray())));

	updateDiscountDistribution(e,sender,recipient,_discountSenderBalance,_discountRecipientBalance,amount);

	uint256 scaledSender_=scaledBalanceOf(sender);
	uint256 scaledRecipient_=scaledBalanceOf(recipient);
	uint256 discountSenderRate_=getUserDiscountRate(sender);
	uint256 discountRecipientRate_=getUserDiscountRate(recipient);
	uint256 discountSenderBalance_=getBalanceOfDiscountToken(e,sender);
	uint256 discountRecipientBalance_=getBalanceOfDiscountToken(e,recipient);

	assert scaledSender_==assert_uint256(_scaledSender-discountScaledSender) && scaledRecipient_==assert_uint256(_scaledRecipient-discountScaledRecipient);

	assert discountSenderRate_==discStrategy.calculateDiscountRate(rayMul(e,scaledSender_,index),assert_uint256(_discountSenderBalance-amount));

	// assert discountRecipientRate_==discStrategy.calculateDiscountRate(assert_uint256(_scaledRecipient-discountScaledRecipient),assert_uint256(_discountRecipientBalance+amount));

	assert discountRecipientRate_==discStrategy.calculateDiscountRate(rayMul(e,scaledRecipient_,index),assert_uint256(_discountRecipientBalance+amount));

	
}

rule unit_burn(){
	address user;
	env e;
	uint256 balanceBefore = balanceOf(e, user);
	uint256 scaledBalanceBefore = scaledBalanceOf(user);
	address caller;
	uint256 amount;
	uint256 i;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	uint256 discountPercent=getUserDiscountRate(user);
	require(getUserCurrentIndex(user) == assert_uint256(2*ray()) && index == assert_uint256(4*ray()));

	uint256 a;uint256 b;
	a,b=getDiscountScaled(e,user,scaledBalanceBefore,discountPercent,i);


	burn(e,user,amount,i);
	uint256 j=getUserCurrentIndex(user);
	storage s=lastStorage;
	rebalanceUserDiscountPercent(e,user);
	storage l=lastStorage;


	//assert rayDiv(e,amount,i)!=0 => scaledBalanceOf(user) < scaledBalanceBefore;
	assert amount==balanceBefore=>scaledBalanceOf(user)==0;
	assert amount!=balanceBefore => scaledBalanceOf(user)== assert_uint256(scaledBalanceBefore - assert_uint256(rayDiv(e,amount,i)+b));

	assert  j==i;
	assert getUserCurrentIndex(user)==index;
	assert i==index => s==l;
	// assert getUserDiscountRate(user)==discStrategy.calculateDiscountRate(e,balanceOf(e,user),discountToken.balanceOf(e,user));
}
rule unit_mint(){
	address user;address x;
	env e;
	uint256 balanceBefore = balanceOf(e, user);
	uint256 scaledBalanceBefore = scaledBalanceOf(user);
	address caller;
	uint256 amount;
	uint256 i;
	uint256 index = indexAtTimestamp(e.block.timestamp);
	uint256 discountPercent=getUserDiscountRate(user);
	require(getUserCurrentIndex(user) == assert_uint256(2*ray()) && index == assert_uint256(4*ray()));

	uint256 a;uint256 b;
	a,b=getDiscountScaled(e,user,scaledBalanceBefore,discountPercent,i);


	mint(e,x,user,amount,i);
	uint256 j=getUserCurrentIndex(user);
	storage s=lastStorage;
	rebalanceUserDiscountPercent(e,user);
	storage l=lastStorage;

	assert  j==i;
	assert getUserCurrentIndex(user)==index;
	assert i==index => s==l;

	// assert getUserDiscountRate(user)==discStrategy.calculateDiscountRate(e,balanceOf(e,user),discountToken.balanceOf(e,user));
}

rule only_discountToken_calls_updateDiscountDistribution(env e,calldataarg args){
	updateDiscountDistribution(e,args);
	assert e.msg.sender==discountToken;
}

rule initialize_integrity(){
	address a;address b;address c;uint8 d;env e;bytes f;
	initialize(e,a,b,c,d,"","",f);
	assert d==decimals(e) && b==UNDERLYING_ASSET_ADDRESS(e) && c==getIncentivesController(e);
}

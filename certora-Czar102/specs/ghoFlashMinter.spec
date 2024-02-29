using GhoToken as gho;
using GhoAToken as atoken;
using MockFlashBorrower as flashBorrower;
using GhoTokenHelper as GhoTokenHelper;

methods{
	function _.isPoolAdmin(address user) external => retreivePoolAdminFromGhost(user) expect bool ALL;
	// function _.onFlashLoan(address, address, uint256, uint256, bytes) external => DISPATCHER(true);
	function _.getACLManager() external => returnACLManager() expect address ALL;

	/********************************;
	*   IERC3156FlashBorrower.sol	*;
	*********************************/  
	function _.isFlashBorrower(address user) external => retreiveFlashBorrowerFromGhost(user) expect bool ALL;
	// Mock specific implementation
	function flashBorrower.action() external returns (MockFlashBorrower.Action) envfree;
	function flashBorrower._transferTo() external returns (address) envfree;
	
	/*********************;
	*	    Tokens       *;
	**********************/  
	function _.burn(uint256) external => DISPATCHER(true);
	function _.mint(address,uint256) external => DISPATCHER(true);
	function _.transfer(address,uint256) external => DISPATCHER(true);
	function _.transferFrom(address,address,uint256) external => DISPATCHER(true);
	function _.balanceOf(address) external => DISPATCHER(true);
	
	/********************************;
	*	    GhoToken.sol	        *;
	*********************************/  
	function gho.burn(uint256) external;
	function gho.mint(address,uint256) external;
	function gho.allowance(address, address) external returns (uint256) envfree;
	function gho.totalSupply() external returns (uint256) envfree;
	function gho.balanceOf(address) external returns (uint256) envfree;
	function gho.transferFrom(address from, address to, uint256 amount) external returns (bool) with (env e) =>
		onTransferFromSummary(e, from, to, amount);

	/********************************;
	*	    GhoAToken.sol	        *;
	*********************************/
	function atoken.getGhoTreasury() external returns (address) envfree;

	/********************************;
	*	    IGhoVariableDebtToken	*;
	*********************************/  
	function _.decreaseBalanceFromInterest(address, uint256) external => NONDET;
	function _.getBalanceFromInterest(address) external => NONDET;

	function getFee() external returns (uint256) envfree;
	function getGhoTreasury() external returns (address) envfree;
	function distributeFeesToTreasury() external envfree;
	function updateFee(uint256) external;
	function updateGhoTreasury(address) external;
	function flashLoan(address,address,uint256,bytes) external returns (bool);
	function maxFlashLoan(address) external returns (uint256) envfree;
	function flashFee(address,uint256) external returns (uint256);

	function ADDRESSES_PROVIDER() external returns (address) envfree;

	function GhoTokenHelper.getFacilitatorBucketLevel(address) external returns (uint256) envfree;
	function GhoTokenHelper.getFacilitatorBucketCapacity(address) external returns uint256 envfree;
	function GhoTokenHelper.askForACLManager(address ap) external returns (address) envfree;
	function GhoTokenHelper.justRevert() external envfree;

	function __passed_ghoToken() external returns (address) envfree;
	function __passed_ghoTreasury() external returns (address) envfree;
	function __passed_fee() external returns (uint) envfree;
	function __passed_addressesProvider() external returns (address) envfree;

	// function onFlashLoan(
	// 	address initiator,
	// 	address token,
	// 	uint256 amount,
	// 	uint256 fee,
	// 	bytes data
	// ) external returns bytes32;

	function _.onFlashLoan(
		address initiator,
		address token,
		uint256 amount,
		uint256 fee,
		bytes data
	) external with (env e) => onFlashLoanSummary(calledContract, e, initiator, token, amount, fee, data) expect (bytes32) ALL;
}

// ---

ghost mathint sumAllBalance {
	init_state axiom sumAllBalance == 0;
}

ghost mapping (address => uint) balanceOf {
	init_state axiom forall address x. balanceOf[x] == 0;
}

hook Sstore gho.balanceOf[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
	require sumAllBalance < 2 ^ 256 && sumAllBalance >= 0;
	require to_mathint(old_balance) <= sumAllBalance;
	sumAllBalance = sumAllBalance + balance - old_balance;
	balanceOf[a] = balance;
	require to_mathint(balance) <= sumAllBalance;
	require sumAllBalance < 2 ^ 256 && sumAllBalance >= 0;
}

hook Sload uint256 balance gho.balanceOf[KEY address a] STORAGE {
	require sumAllBalance < 2 ^ 256 && sumAllBalance >= 0;
	require balanceOf[a] == balance;
	require to_mathint(balance) <= sumAllBalance;
}

// ---

ghost bool careAboutParamChanges;

function onFlashLoanSummary(
	address receiver,
	env e,
	address initiator,
	address token,
	uint amount,
	uint fee,
	bytes data
) returns bytes32 {
	flashCallbackDone = true;

	assert getFee() == lastFee || !careAboutParamChanges, "fee changed before flash loan";
	assert getGhoTreasury() == lastTreasury || !careAboutParamChanges, "treasury changed before flash loan";
	flashLoanDepth = flashLoanDepth + 1;
	lastCheckDepth = flashLoanDepth;
	bytes32 res2 = flashBorrower.onFlashLoan@withrevert(e, initiator, token, amount, fee, data);
	bool reverted = lastReverted;
	flashCallbackReverted = reverted || res2 != to_bytes32(0x439148f0bbc682ca079e46d6e2c2f0c1e3b820f1a291b069d8882abf8cf18dd9);
	lastFee = getFee();
	lastTreasury = getGhoTreasury();
	flashLoanDepth = flashLoanDepth - 1;
	lastCheckDepth = flashLoanDepth;

	if (reverted || receiver == currentContract) {
		GhoTokenHelper.justRevert();
	}

	return res2;
}

function onTransferFromSummary(
	env e,
	address from,
	address to,
	uint amt
) returns bool {
	flashTransferDone = true;
	bool res = gho.transferFrom@withrevert(e, from, to, amt);
	flashTransferReverted = lastReverted && res;

	if (lastReverted) {
		GhoTokenHelper.justRevert();
	}

	return res;
}

ghost bool flashCallbackReverted;
ghost bool flashTransferReverted;
ghost bool flashCallbackDone;
ghost bool flashTransferDone;

ghost bool askedForACLManager {
	init_state axiom !askedForACLManager;
}

function returnACLManager() returns address {
	askedForACLManager = true;

	// NONDET implementation
	address a;
	return a;
}

ghost mathint flashLoanDepth {
	init_state axiom flashLoanDepth == 0;
}

/**
* @title proves that the depth of the flash loan is alwayszero from teh outside perspective
**/
invariant flashLoanDepthIsZero()
	flashLoanDepth == 0
	{
		preserved {
			require careAboutParamChanges == false;
		}
	}


// keeps track of users with pool admin permissions in order to return a consistent value per user
ghost mapping(address => bool) poolAdmin_ghost;

// keeps track of users with flash borrower permissions in order to return a consistent value per user
ghost mapping(address => bool) flashBorrower_ghost;

// returns whether the user is a pool admin
function retreivePoolAdminFromGhost(address user) returns bool{
	return poolAdmin_ghost[user];
}

// returns whether the user is a flash borrower
function retreiveFlashBorrowerFromGhost(address user) returns bool{
	return flashBorrower_ghost[user];
}

// a set of assumptions needed for rules that call flashloan
function flashLoanReqs(env e){
	require e.msg.sender != currentContract;
	require gho.allowance(currentContract, e.msg.sender) == 0;
}

// an assumption that demands the sum of balances of 3 given users is no more than the total supply
function ghoBalanceOfThreeUsersLETotalSupply(address user1, address user2, address user3) {
	require gho.balanceOf(user1) + gho.balanceOf(user2) + gho.balanceOf(user3) <= to_mathint(gho.totalSupply());
}

/**
 * @title The GHO balance of the flash minter should grow when calling any function, excluding distributeFees
 */
rule balanceOfFlashMinterGrows(method f, env e, calldataarg args) 
	filtered { f -> f.selector != sig:distributeFeesToTreasury().selector } {
	requireInvariant fee_less_than_MAX_FEE();

	careAboutParamChanges = false;
	
	// No overflow of gho is possible
	ghoBalanceOfThreeUsersLETotalSupply(currentContract, e.msg.sender, atoken);
	flashLoanReqs(e);
	// excluding calls to distribute fees
	mathint action = assert_uint256(flashBorrower.action());
	require action != 1; 

	uint256 _facilitatorBalance = gho.balanceOf(currentContract);

	f(e, args);

	uint256 facilitatorBalance_ = gho.balanceOf(currentContract);

	assert facilitatorBalance_ >= _facilitatorBalance;
}

/**
 * @title Checks the integrity of updateGhoTreasury - after update the given address is set
 */
rule integrityOfTreasurySet(address token){
	env e;
	updateGhoTreasury(e, token);
	address treasury_ = getGhoTreasury(e);
	assert treasury_ == token;
}

/**
 * @title Checks the integrity of updateFee - after update the given value is set
 */
rule integrityOfFeeSet(uint256 new_fee){
	env e;
	updateFee(e, new_fee);
	uint256 fee_ = getFee(e);
	assert fee_ == new_fee;
}

/**
 * @title Checks that the available liquidity, retreived by maxFlashLoan, stays the same after any action 
 */
rule availableLiquidityDoesntChange(method f, address token){
	careAboutParamChanges = false;
	requireInvariant fee_less_than_MAX_FEE();
	env e; calldataarg args;
	uint256 _liquidity = maxFlashLoan(e, token);

	f(e, args);

	uint256 liquidity_ = maxFlashLoan(e, token);

	assert liquidity_ == _liquidity;
}

/**
 * @title Checks the integrity of distributeFees:
 *        1. As long as the treasury contract itself isn't acting as a flashloan minter, the flashloan facilitator's GHO balance should be empty after distribution
 *        2. The change in balances of the receiver (treasury) and the sender (flash minter) is the same. i.e. no money is being generated out of thin air
 */
rule integrityOfDistributeFeesToTreasury(){
	env e;
	address treasury = getGhoTreasury(e);
	uint256 _facilitatorBalance = gho.balanceOf(currentContract);
	uint256 _treasuryBalance = gho.balanceOf(treasury);

	// No overflow of gho is possible
	ghoBalanceOfThreeUsersLETotalSupply(currentContract, treasury, atoken);
	distributeFeesToTreasury(e);

	uint256 facilitatorBalance_ = gho.balanceOf(currentContract);
	uint256 treasuryBalance_ = gho.balanceOf(treasury);

	assert treasury != currentContract => facilitatorBalance_ == 0;
	assert treasuryBalance_ - _treasuryBalance == _facilitatorBalance - facilitatorBalance_;
}

/**
 * @title Checks that the fee amount reported by flashFee is the the same as the actual fee that is taken by flashloaning
 */
rule feeSimulationEqualsActualFee(address receiver, address token, uint256 amount, bytes data){
	requireInvariant fee_less_than_MAX_FEE();
	careAboutParamChanges = false;
	env e;
	mathint feeSimulationResult = flashFee(e, token, amount);
	uint256 _facilitatorBalance = gho.balanceOf(currentContract);
	
	flashLoanReqs(e);
	require atoken.getGhoTreasury() != currentContract;
	// No overflow of gho is possible
	ghoBalanceOfThreeUsersLETotalSupply(currentContract, e.msg.sender, atoken);
	// Excluding call to distributeFeesToTreasury & calling another flashloan (which will generate another fee in recursion)
	mathint borrower_action = assert_uint256(flashBorrower.action());
	require borrower_action != 1 && borrower_action != 0;
	// Because we calculate the actual fee by balance difference of the minter, we assume no extra money is being sent to the minter.
	require flashBorrower._transferTo() != currentContract;
	
	flashLoan(e, receiver, token, amount, data);

	uint256 facilitatorBalance_ = gho.balanceOf(currentContract);

	mathint actualFee = facilitatorBalance_ - _facilitatorBalance;

	assert feeSimulationResult == actualFee;
}

/**
* @title proves that the fee is always less than the max fee
**/
invariant fee_less_than_MAX_FEE()
	getFee() <= 10000
	{
		preserved {
			require careAboutParamChanges == false;
		}
	}


/**
* @title proves that the bucket level stays zero
**/
invariant debt_stays_zero()
	GhoTokenHelper.getFacilitatorBucketLevel(currentContract) == 0
	{
		preserved {
			require careAboutParamChanges == false;
		}
	}

ghost uint lastFee;
ghost address lastTreasury;
ghost mathint lastCheckDepth;

/**
* @title Main rule constraining revert reasons and implied state changes of functions.
* Also checks that the functions don't modify the state they shouldn't.
**/
rule main(method f) {
	uint feeBefore = getFee();
	address treasuryBefore = getGhoTreasury();
	bool skipFeeCheck = false;
	bool skipTreasuryCheck = false;

	address ghoTokenBalanceNotChanged;
	uint ghoTokenInitialBalance = gho.balanceOf(ghoTokenBalanceNotChanged);
	bool skipBalanceCheck = false;

	requireInvariant fee_less_than_MAX_FEE();
	requireInvariant flashLoanDepthIsZero();

	env e; calldataarg arg;

	if (f.selector == sig:flashLoan(address,address,uint256,bytes).selector) {
		// for now, anything can happen here
		// revert reasoning needs to be added
		lastFee = getFee();
		lastTreasury = getGhoTreasury();
		flashCallbackDone = false;
		flashTransferDone = false;

		address receiver;
		address token;
		uint amt;
		bytes data;
		require data.length < 2 ^ 32;

		uint maxLoan = maxFlashLoan(token);

		flashLoan@withrevert(e, receiver, token, amt, data);
		bool reverted = lastReverted;

		assert reverted <=> (
			flashCallbackReverted ||
			flashTransferReverted ||
			token != gho ||
			amt > maxLoan ||
			amt == 0 ||
			gho.totalSupply() + amt >= 2 ^ 256 ||
			e.msg.value != 0
		);

		assert !reverted => (
			getFee() == lastFee &&
			getGhoTreasury() == lastTreasury
		);

		skipFeeCheck = true;
		skipTreasuryCheck = true;
		skipBalanceCheck = true;
		// do flash loan check
	} else if (f.selector == sig:distributeFeesToTreasury().selector) {
		uint balanceBefore = gho.balanceOf(currentContract);
		uint treasuryBalanceBefore = gho.balanceOf(treasuryBefore);

		require treasuryBefore != currentContract => (
			treasuryBefore != ghoTokenBalanceNotChanged &&
			currentContract != ghoTokenBalanceNotChanged
		);

		address whatever;

		ghoBalanceOfThreeUsersLETotalSupply(currentContract, treasuryBefore, whatever);

		distributeFeesToTreasury@withrevert();

		assert !lastReverted;

		assert getGhoTreasury() != currentContract => (
			gho.balanceOf(currentContract) == 0 &&
			to_mathint(gho.balanceOf(treasuryBefore)) == treasuryBalanceBefore + balanceBefore
		);
	} else if (f.selector == sig:updateFee(uint256).selector) {
		skipFeeCheck = true;
		uint newFee;

		updateFee@withrevert(e, newFee);
		bool reverted = lastReverted;

		assert reverted <=> (
			newFee > 10000 ||
			!poolAdmin_ghost[e.msg.sender] ||
			e.msg.value != 0
		);

		assert !reverted => getFee() == newFee;
	} else if (f.selector == sig:updateGhoTreasury(address).selector) {
		skipTreasuryCheck = true;
		address newTreasury;

		updateGhoTreasury@withrevert(e, newTreasury);
		bool reverted = lastReverted;

		assert reverted <=> (
			!poolAdmin_ghost[e.msg.sender] ||
			e.msg.value != 0
		);

		assert !reverted => getGhoTreasury() == newTreasury;
	} else if (f.selector == sig:maxFlashLoan(address).selector) {
		address token;

		uint maxLoan = maxFlashLoan@withrevert(token);

		assert !lastReverted;

		uint bucketLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
		uint bucketCapacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);

		assert maxLoan == (token == gho ?
			(bucketLevel > bucketCapacity ? 0 : assert_uint256(bucketCapacity - bucketLevel)) :
			0
		);
	} else if (f.selector == sig:flashFee(address,uint256).selector) {
		address token;
		uint amount;

		uint fee = flashFee@withrevert(e, token, amount);
		bool reverted = lastReverted;

		assert reverted <=> (
			token != gho ||
			(getFee() == 0 || flashBorrower_ghost[e.msg.sender] ?
				false :
				amount > assert_uint256((max_uint256 - 5000) / getFee())
			) ||
			e.msg.value != 0
		);

		assert !reverted => fee == (flashBorrower_ghost[e.msg.sender] ?
			0 :
			assert_uint256((getFee() * amount + 5000) / 10000)
		);
	} else if (f.selector == sig:getFee().selector) {
		getFee@withrevert();
		assert !lastReverted;
	} else if (f.selector == sig:getGhoTreasury().selector) {
		getGhoTreasury@withrevert();
		assert !lastReverted;
	} else {
		f@withrevert(e, arg);
	}

	assert (
		(getFee() == feeBefore || skipFeeCheck) &&
		(getGhoTreasury() == treasuryBefore || skipTreasuryCheck) &&
		(gho.balanceOf(ghoTokenBalanceNotChanged) == ghoTokenInitialBalance || skipBalanceCheck)
	);
}

// invariant constructor_integrity()
// 	__passed_ghoToken() == gho &&
// 		__passed_ghoTreasury() == getGhoTreasury() &&
// 		__passed_fee() == getFee() &&
// 		__passed_addressesProvider() == ADDRESSES_PROVIDER() &&
// 		askedForACLManager
// 	{ preserved {require false;} }

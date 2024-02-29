using GhoToken as gho;
using GhoAToken as atoken;
using MockFlashBorrower as flashBorrower;

methods{
    function getFee() external returns (uint256) envfree;
    function getGhoTreasury() external returns (address) envfree;
    function maxFlashLoan(address) external returns (uint256) envfree;
    function getFee() external returns (uint256) envfree;
    function MAX_FEE() external returns (uint256) envfree;

    function _.isPoolAdmin(address user) external => retreivePoolAdminFromGhost(user) expect bool ALL;
    function _.onFlashLoan(address, address, uint256, uint256, bytes) external => DISPATCHER(true);
    function _.getACLManager() external => NONDET;

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
    function _.burn(uint256)  external=> DISPATCHER(true);
    function _.mint(address, uint256)  external=> DISPATCHER(true);
    function _.transfer(address, uint256) external => DISPATCHER(true);
    function _.balanceOf(address) external => DISPATCHER(true);
    
    /********************************;
	*	    GhoToken.sol	        *;
	*********************************/  
    function gho.allowance(address, address) external returns (uint256) envfree;
    function gho.totalSupply() external returns (uint256) envfree;
    function gho.balanceOf(address) external returns (uint256) envfree;
    function gho.getFacilitatorBucket(address) external returns (uint256, uint256) envfree;

    /********************************;
	*	    GhoAToken.sol	        *;
	*********************************/
    function atoken.getGhoTreasury() external returns (address) envfree;

    /********************************;
	*	    IGhoVariableDebtToken	*;
	*********************************/  
    function _.decreaseBalanceFromInterest(address, uint256) external => NONDET;
    function _.getBalanceFromInterest(address) external => NONDET;
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
function ghoBalanceOfTwoUsersLETotalSupply(address user1, address user2, address user3){
    require gho.balanceOf(user1) + gho.balanceOf(user2) + gho.balanceOf(user3) <= to_mathint(gho.totalSupply());
}

/**
 * @title The GHO balance of the flash minter should grow when calling any function, excluding distributeFees
 */
rule balanceOfFlashMinterGrows(method f, env e, calldataarg args) 
    filtered { f -> f.selector != sig:distributeFeesToTreasury().selector }{
    
    // No overflow of gho is possible
    ghoBalanceOfTwoUsersLETotalSupply(currentContract, e.msg.sender, atoken);
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
 * @title Checks the integrity of fee - fee can never exceed MAX_FEE.
 */
invariant feeLEMaxFee()
   getFee() <= MAX_FEE();

/**
 * @title Checks that the available liquidity, retreived by maxFlashLoan, stays the same after any action 
 */
rule availableLiquidityDoesntChange(method f, address token){
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
    ghoBalanceOfTwoUsersLETotalSupply(currentContract, treasury, atoken);
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
    env e;
    mathint feeSimulationResult = flashFee(e, token, amount);
    uint256 _facilitatorBalance = gho.balanceOf(currentContract);
    
    flashLoanReqs(e);
    require atoken.getGhoTreasury() != currentContract;
    // No overflow of gho is possible
    ghoBalanceOfTwoUsersLETotalSupply(currentContract, e.msg.sender, atoken);
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
 * @title Checks that flashLoan() reverts when the given token is not the GhoToken.
 */
rule flashLoanShouldRevertWhenWrongToken(
    env e,
    address receiver,
    address token,
    uint256 amount,
    bytes data
) {
    require token != gho;
    flashLoan@withrevert(e, receiver, token, amount, data);
    assert lastReverted;
}

/**
* @title The fee value(`_fee`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule feeCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	mathint feeBefore = getFee();

	f(e, args);

	mathint feeAfter = getFee();

	assert !isAdmin => feeAfter == feeBefore;
}

/**
* @title The ghoTreasury address(`_ghoTreasury`) can only be changed by a msg.sender holding the PoolAdmin role.
*/
rule ghoTreasuryCanOnlyBeChangedByPoolAdmin(
	env e,
	method f,
	calldataarg args
) {
	bool isAdmin = poolAdmin_ghost[e.msg.sender];
	address ghoTreasuryBefore = getGhoTreasury();

	f(e, args);

	address ghoTreasuryAfter = getGhoTreasury();

	assert !isAdmin => ghoTreasuryAfter == ghoTreasuryBefore;
}

/**
 * @title Checks that the total amount loaned by flashLoan() does not exceed maxFlashLoan().
 */
rule userCannotExceedMaxAmountLoaned(address receiver, address token, uint256 amount, bytes data)
{
    env e;

    uint256 ghoLevel; uint256 ghoCapacity;
    ghoCapacity, ghoLevel = gho.getFacilitatorBucket(e, currentContract);
    require ghoLevel <= ghoCapacity;

    // Set the mock-contracts helper variables to zero.
    require flashBorrower.accumulatedAmount(e) == 0;

    flashLoanReqs(e);

    mathint maxAmount = maxFlashLoan(e, token);

    flashLoan(e, receiver, token, amount, data);

    mathint totalAmount = flashBorrower.accumulatedAmount(e);

    assert totalAmount <= maxAmount;
}

/**
 * @title Checks that the fee payed for the total amount loaned by flashLoan() is the expected amount.
 */
rule userCannotReduceFee(address receiver, address token, uint256 amount, bytes data)
{
    uint256 totalAmount;
    env e;
    uint256 feeSimulationResult = flashFee(e, token, totalAmount);

    uint256 ghoLevel; uint256 ghoCapacity;
    ghoCapacity, ghoLevel = gho.getFacilitatorBucket(e, currentContract);
    require ghoLevel <= ghoCapacity;

    // Set the mock-contracts helper variables to zero.
    require flashBorrower.accumulatedAmount(e) == 0;
    require flashBorrower.accumulatedFee(e) == 0;

    flashLoanReqs(e);

    flashLoan(e, receiver, token, amount, data);

    assert (totalAmount == flashBorrower.accumulatedAmount(e))
        => (flashBorrower.accumulatedFee(e) == feeSimulationResult)
        || (flashBorrower.accumulatedFee(e) == require_uint256(feeSimulationResult +1))
        || (flashBorrower.accumulatedFee(e) == require_uint256(feeSimulationResult -1));
}

/**
 * @title Checks that the balance of the faciliator does not decrease, unless gho is transfered to the treasury.
 */
rule userCannotStealFundsWithFlashLoan(address receiver, address token, uint256 amount, bytes data)
{
    env e;
    address treasury = getGhoTreasury(e);
    require treasury == atoken.getGhoTreasury(e);
    require receiver != treasury;
    require treasury != currentContract && treasury != receiver;
    require gho.balanceOf(currentContract) + gho.balanceOf(treasury) + gho.balanceOf(e.msg.sender) + gho.balanceOf(receiver) <= to_mathint(gho.totalSupply());

    mathint facilitatorBalanceBefore = gho.balanceOf(currentContract);
    mathint treasuryBalanceBefore = gho.balanceOf(treasury);

    uint256 ghoLevel; uint256 ghoCapacity;
    ghoCapacity, ghoLevel = gho.getFacilitatorBucket(e, currentContract);
    require ghoLevel <= ghoCapacity;

    // set to zero before call (does not affect correctness)
    require flashBorrower.accumulatedFee(e) == 0;

    flashLoanReqs(e);
    require atoken.getGhoTreasury() != currentContract;
    // No overflow of gho is possible
    ghoBalanceOfTwoUsersLETotalSupply(currentContract, e.msg.sender, atoken);
    // Because we calculate the actual fee by balance difference of the minter, we assume no extra money is being sent to the minter.
    require flashBorrower._transferTo() != currentContract;

    flashLoan(e, receiver, token, amount, data);

    mathint facilitatorBalanceAfter = gho.balanceOf(currentContract);
    mathint treasuryBalanceAfter = gho.balanceOf(treasury);
    mathint treasuryDelta = treasuryBalanceAfter - treasuryBalanceBefore;

    assert (treasuryDelta >= 0) =>facilitatorBalanceAfter + treasuryDelta >= facilitatorBalanceBefore + flashBorrower.accumulatedFee(e);
}

/**
 * @title The fee should not decrease when the amount of to be loaned increases.
 */
rule feeGrowsContinuously(address token, uint256 smallerAmount, uint256 biggerAmount)
{
    env e;

    require smallerAmount < biggerAmount;

    uint256 smallerfeeSimulationResult = flashFee(e, token, smallerAmount);
    uint256 biggerfeeSimulationResult = flashFee(e, token, biggerAmount);

    assert smallerfeeSimulationResult <= biggerfeeSimulationResult;
}

/**
 * @title The fee should not decrease when the amount of to be loaned increases.
 */
rule additivityOfFee(
    address token,
    uint256 amountA,
    uint256 amountB
) {
    env e;
    uint256 amountAplusB = require_uint256(amountA + amountB);

    mathint feeA = flashFee(e, token, amountA);
    mathint feeB = flashFee(e, token, amountB);
    mathint feeAplusB = flashFee(e, token, amountAplusB);

     assert feeA + feeB == feeAplusB ||  feeA + feeB + 1 == feeAplusB || feeA + feeB - 1 == feeAplusB;
}

/**
 * @title maxFlashLoan() returns the expected value.
 */
rule maxFlashLoanCorrectness(
    address token
) {
    uint256 ghoLevel; uint256 ghoCapacity;
    ghoCapacity, ghoLevel = gho.getFacilitatorBucket(currentContract);
    require ghoLevel <= ghoCapacity;

    mathint returnedValue = maxFlashLoan(token);



    assert (token != gho) => (returnedValue == 0);
    assert (token == gho) => (returnedValue == ((ghoCapacity > ghoLevel) ? (ghoCapacity - ghoLevel) : 0));
}

/**
 * @title flashFee() returns the expected value.
 */
rule flashFeeCorrectness(
    env e,
    address token,
    uint256 amount
) {
    bool isBorrower = flashBorrower_ghost[e.msg.sender];
    mathint fee = getFee();

    mathint returnedValue = flashFee(e, token, amount);

    assert token == gho;
    assert isBorrower => (returnedValue == 0);
    assert (!isBorrower)=> (returnedValue == (((amount * fee) + 5000)/ 10000));
}

/**
 * @title All functions can be executed.
 */
rule sanity {
  env e;
  calldataarg arg;
  method f;
  f(e, arg);
  satisfy true;
}

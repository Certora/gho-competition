using GhoToken as gho;
using GhoAToken as atoken;
using MockFlashBorrower as flashBorrower;

methods{
    function _.isPoolAdmin(address user) external => retreivePoolAdminFromGhost(user) expect bool ALL;
    function _.onFlashLoan(address, address, uint256, uint256, bytes) external => DISPATCHER(true);
    function _.getACLManager() external => NONDET;

    /********************************;
	*   GhoFlashMinterHarness.sol	*;
	*********************************/  
    function percentMul(uint256, uint256) external returns(uint256) envfree;

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

definition notHarnessCall(method f) returns bool = 
    (f.selector != sig:percentMul(uint256,uint256).selector
    && f.selector != sig:isFlashBorrower(address).selector
    && f.selector != sig:isPoolAdmin(address).selector);

// keeps track of ACL to check if user is flash borrower
ghost ghostIsFlashBorrower(address) returns bool;

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
    bool isAdmin = isPoolAdmin(e, e.msg.sender);
    updateGhoTreasury@withrevert(e, token);
    bool lastRev = lastReverted;
    assert (!isAdmin || e.msg.value > 0) <=> lastRev;
    address treasury_ = getGhoTreasury(e);
    assert !lastRev => treasury_ == token;
}

/**
 * @title Checks that if caller is not admin, calls to updateFee and updateGhoTreasury always revert
 */
rule onlyAdminFunctionsConsistency(method f)
    filtered { f -> (
        f.selector == sig:updateFee(uint256).selector || 
        f.selector == sig:updateGhoTreasury(address).selector
    ) }{
    env e;
    calldataarg args;
    require !isPoolAdmin(e, e.msg.sender);
    f@withrevert(e, args);
    assert lastReverted;
}

/**
 * @title Checks the integrity of updateFee - after update the given value is set
 */
rule integrityOfFeeSet(uint256 new_fee){
    env e;
    bool isAdmin = isPoolAdmin(e, e.msg.sender);
    updateFee@withrevert(e, new_fee);
    bool lastRev = lastReverted;
    uint256 fee_ = getFee(e);
    assert (e.msg.value > 0 || !isAdmin || new_fee > MAX_FEE(e)) <=> lastRev;
    assert !lastRev => fee_ == new_fee;
}

/**
 * @title Checks the integrity of flashFee - reverts for non gho tokens and returns flash fee to flah borrowers (0 otherwise)
 */
rule integrityOfFlashFee(address token, uint256 amount){
    env e;
    uint256 fee = flashFee@withrevert(e, token, amount);
    bool lastRev = lastReverted;
    uint percentFee = percentMul(amount, getFee(e));
    assert (token != gho || e.msg.value > 0) <=> lastRev;
    assert !lastRev && isFlashBorrower(e, e.msg.sender) => fee == 0;
    assert !lastRev && !isFlashBorrower(e, e.msg.sender) => fee == percentFee;
}

/**
 * @title Checks the integrity of maxFlashLoan - returns 0 for tokens != GHO_TOKEN and returns the calculation otherwise
 */
rule integrityOfMaxFlashLoan(address token){
    env e;
    uint256 ret = maxFlashLoan@withrevert(e, token);
    bool lastRev = lastReverted;
    uint256 capacity;
    uint256 level;
    capacity, level = gho.getFacilitatorBucket(e, currentContract);

    assert (e.msg.value > 0) <=> lastRev;
    assert token != gho => ret == 0;
    assert token == gho => to_mathint(ret) == (capacity > level ? capacity - level : 0);
}

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


rule sanity {
  env e;
  calldataarg arg;
  method f;
  f(e, arg);
  satisfy true;
}


/**
* @notice Consistency check for the execution of function distributeFeesToTreasury
*/
rule distributeFeesToTreasuryConsistencyCheck(env e) {

	address treasury = getGhoTreasury(e);
	uint256 balancePre = gho.balanceOf(currentContract);
	uint256 balanceTreasuryPre = gho.balanceOf(treasury);

	require treasury != currentContract;

    distributeFeesToTreasury@withrevert(e);
    bool lastRev = lastReverted;

	uint256 balancePost = gho.balanceOf(currentContract);
	uint256 balanceTreasuryPost = gho.balanceOf(treasury);

    assert lastRev <=> e.msg.value > 0;
    assert !lastRev => (
		balancePost == 0 &&
		balanceTreasuryPost == require_uint256(balancePre + balanceTreasuryPre)
	);
}

methods{

    // ScaledBalanceTokenBase
    function scaledBalanceOf(address) external returns (uint256) envfree;
    function getScaledUserBalanceAndSupply(address user) external returns (uint256, uint256) envfree;
    function scaledTotalSupply() internal returns (uint256);
    function getPreviousIndex(address user) external returns (uint256) envfree;
    function _mintScaled(address caller, address onBehalfOf, uint256 amount, uint256 index) internal returns (bool); // overridden GhoVariableDebtToken
    function _burnScaled(address user, address target, uint256 amount, uint256 index) internal; // overridden GhoVariableDebtToken
    function _transfer(address sender, address recipient, uint256 amount, uint256 index) internal;

    // IncentivizedERC20
    function name() internal returns (string memory);
    function symbol() external returns (string memory) envfree;
    function decimals() external returns (uint8) envfree;
    function totalSupply() internal returns (uint256); // overridden in GhoAToken, GhoVariableDebtToken
    function balanceOf(address account) internal returns (uint256); // overridden in GhoAToken, GhoVariableDebtToken
    function getIncentivesController() external returns (address) envfree;
    function setIncentivesController(address controller) external;
    function transfer(address recipient, uint256 amount) external returns (bool); // Always reverts
    function allowance(address owner, address spender) external returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool); // Always reverts
    function increaseAllowance(address spender, uint256 addedValue) external returns (bool);
    function decreaseAllowance(address spender, uint256 subtractedValue) external returns (bool);
    function _transfer(address sender, address recipient, uint128 amount) internal; // overridden in GhoAToken
    function _setName(string memory newName) internal;
    function _setSymbol(string memory newSymbol) internal;
    function _setDecimals(uint8 newDecimals) internal;
}
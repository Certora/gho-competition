pragma solidity 0.8.10;

import {GhoVariableDebtToken} from '../../src/contracts/facilitators/aave/tokens/GhoVariableDebtToken.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {IACLManager} from '@aave/core-v3/contracts/interfaces/IACLManager.sol';
import {WadRayMath} from '@aave/core-v3/contracts/protocol/libraries/math/WadRayMath.sol';

contract GhoVariableDebtTokenHarness is GhoVariableDebtToken {
  using WadRayMath for uint256;

  constructor(IPool pool) public GhoVariableDebtToken(pool) {
    //nop
  }

  function getUserCurrentIndex(address user) external view returns (uint256) {
    return _userState[user].additionalData;
  }

  function getUserDiscountRate(address user) external view returns (uint256) {
    return _ghoUserState[user].discountPercent;
  }

  function getUserAccumulatedDebtInterest(address user) external view returns (uint256) {
    return _ghoUserState[user].accumulatedDebtInterest;
  }

  function scaledBalanceOfToBalanceOf(uint256 bal) public view returns (uint256) {
    return bal.rayMul(POOL.getReserveNormalizedVariableDebt(_underlyingAsset));
  }

  function getBalanceOfDiscountToken(address user) external returns (uint256) {
    return _discountToken.balanceOf(user);
  }

  //
  // Added functions
  //

  function getRevisionHarness() external pure returns (uint256) {
    return getRevision();
  }

  function getPoolAddress() external view returns (address) {
    return address(POOL);
  }

  function calculateDomainSeparator() external view returns (bytes32) {
    return _calculateDomainSeparator();
  }

  function isPoolAdmin(address account) external view returns (bool) {
    IACLManager aclManager = IACLManager(_addressesProvider.getACLManager());
    return aclManager.isPoolAdmin(account);
  }

  function setName1() external {
    string memory anotherName = 'name1';
    _setName(anotherName);
  }

  function setName2() external {
    string memory anotherName = 'name2';
    _setName(anotherName);
  }
}

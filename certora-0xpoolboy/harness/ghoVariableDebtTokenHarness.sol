pragma solidity 0.8.10;

import {GhoVariableDebtToken} from '../../src/contracts/facilitators/aave/tokens/GhoVariableDebtToken.sol';
import {WadRayMath} from '@aave/core-v3/contracts/protocol/libraries/math/WadRayMath.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {PercentageMath} from '@aave/core-v3/contracts/protocol/libraries/math/PercentageMath.sol';

contract GhoVariableDebtTokenHarness is GhoVariableDebtToken {
  using WadRayMath for uint256;
  using PercentageMath for uint256;

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

  function rayMul(uint256 x, uint256 y) external view returns (uint256) {
    return x.rayMul(y);
  }

  function rayDiv(uint256 x, uint256 y) external view returns (uint256) {
    return x.rayDiv(y);
  }

  function getBalanceIncreaseAndDiscountScaled(
    address user,
    uint256 previousScaledBalance,
    uint256 discountPercent,
    uint256 index
  ) external view returns (uint256, uint256) {
    uint256 balanceIncrease = previousScaledBalance.rayMul(index) -
      previousScaledBalance.rayMul(_userState[user].additionalData);

    uint256 discountScaled = 0;
    if (balanceIncrease != 0 && discountPercent != 0) {
      uint256 discount = balanceIncrease.percentMul(discountPercent);
      discountScaled = discount.rayDiv(index);
      balanceIncrease = balanceIncrease - discount;
    }

    return (balanceIncrease, discountScaled);
  }
}

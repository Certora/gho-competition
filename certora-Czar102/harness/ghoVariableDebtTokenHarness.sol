pragma solidity 0.8.10;

import {GhoVariableDebtToken} from '../../src/contracts/facilitators/aave/tokens/GhoVariableDebtToken.sol';
import {WadRayMath} from '@aave/core-v3/contracts/protocol/libraries/math/WadRayMath.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {SafeCast} from '@aave/core-v3/contracts/dependencies/openzeppelin/contracts/SafeCast.sol';

contract GhoVariableDebtTokenHarness is GhoVariableDebtToken {
  using WadRayMath for uint256;
  using SafeCast for uint256;

  constructor(IPool pool) public GhoVariableDebtToken(pool) {
    //nop
  }

  function getUserCurrentIndex(address user) public view returns (uint256) {
    return _userState[user].additionalData;
  }

  function getUserDiscountRate(address user) public view returns (uint256) {
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

  function accrueDebt(address user) external returns (uint256, uint256) {
    (uint256 balanceIncrease, uint256 discountScaled) = _accrueDebtOnAction(
      user,
      balanceOf(user),
      getUserDiscountRate(user),
      POOL.getReserveNormalizedVariableDebt(_underlyingAsset)
    );
    _burn(user, discountScaled.toUint128());
    return (balanceIncrease, discountScaled);
  }

  function refreshDiscountPercent(address user, uint256 discountTokenBalance) external {
    _refreshDiscountPercent(user, balanceOf(user), discountTokenBalance, getUserDiscountRate(user));
  }
}

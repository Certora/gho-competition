import {GhoDiscountRateStrategy} from '../munged/contracts/facilitators/aave/interestStrategy/GhoDisπGhcountRateStrategy.sol';
import {WadRayMath} from '@aave/core-v3/contracts/protocol/libraries/math/WadRayMath.sol';

contract GhoDiscountRateStrategyHarness is GhoDiscountRateStrategy {
  using WadRayMath for uint256;
}

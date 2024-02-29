pragma solidity ^0.8.0;

import {IACLManager} from '@aave/core-v3/contracts/interfaces/IACLManager.sol';
import {IPoolAddressesProvider} from '@aave/core-v3/contracts/interfaces/IPoolAddressesProvider.sol';
import {GhoFlashMinter} from '../../src/contracts/facilitators/flashMinter/GhoFlashMinter.sol';

contract GhoFlashMinterHarness is GhoFlashMinter {
  uint256 internal constant PERCENTAGE_FACTOR = 1e4;
  // Half percentage factor (50.00%)
  uint256 internal constant HALF_PERCENTAGE_FACTOR = 0.5e4;

  constructor(
    address ghoToken,
    address ghoTreasury,
    uint256 fee,
    address addressesProvider
  ) GhoFlashMinter(ghoToken, ghoTreasury, fee, addressesProvider) {}

  function percentMul(uint256 value, uint256 percentage) external pure returns (uint256 result) {
    // to avoid overflow, value <= (type(uint256).max - HALF_PERCENTAGE_FACTOR) / percentage
    assembly {
      if iszero(
        or(
          iszero(percentage),
          iszero(gt(value, div(sub(not(0), HALF_PERCENTAGE_FACTOR), percentage)))
        )
      ) {
        revert(0, 0)
      }

      result := div(add(mul(value, percentage), HALF_PERCENTAGE_FACTOR), PERCENTAGE_FACTOR)
    }
  }

  function isFlashBorrower(address who) external returns (bool) {
    IACLManager ACL_M = IACLManager(IPoolAddressesProvider(ADDRESSES_PROVIDER).getACLManager());
    return ACL_M.isFlashBorrower(who);
  }

  function isPoolAdmin(address who) external returns (bool) {
    IACLManager ACL_M = IACLManager(IPoolAddressesProvider(ADDRESSES_PROVIDER).getACLManager());
    return ACL_M.isPoolAdmin(who);
  }
}

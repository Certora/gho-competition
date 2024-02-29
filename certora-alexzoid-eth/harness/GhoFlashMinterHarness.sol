pragma solidity ^0.8.0;

import {GhoFlashMinter} from '../../src/contracts/facilitators/flashMinter/GhoFlashMinter.sol';

contract GhoFlashMinterHarness is GhoFlashMinter {
  constructor(
    address ghoToken,
    address ghoTreasury,
    uint256 fee,
    address addressesProvider
  ) GhoFlashMinter(ghoToken, ghoTreasury, fee, addressesProvider) {}

  // just in case needed
}

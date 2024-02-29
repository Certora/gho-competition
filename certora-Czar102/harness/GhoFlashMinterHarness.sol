import {GhoFlashMinter} from '../../src/contracts/facilitators/flashMinter/GhoFlashMinter.sol';

contract GhoFlashMinterHarness is GhoFlashMinter {
  address public __passed_ghoToken;
  address public __passed_ghoTreasury;
  uint public __passed_fee;
  address public __passed_addressesProvider;

  constructor(
    address ghoToken,
    address ghoTreasury,
    uint256 fee,
    address addressesProvider
  ) GhoFlashMinter(ghoToken, ghoTreasury, fee, addressesProvider) {
    __passed_ghoToken = ghoToken;
    __passed_ghoTreasury = ghoTreasury;
    __passed_fee = fee;
    __passed_addressesProvider = addressesProvider;
  }
}

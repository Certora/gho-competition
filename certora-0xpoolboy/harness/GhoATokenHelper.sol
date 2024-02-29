pragma solidity ^0.8.0;

import {IGhoAToken} from '../../src/contracts/facilitators/aave/tokens/interfaces/IGhoAToken.sol';
import {GhoAToken} from '../../src/contracts/facilitators/aave/tokens/GhoAToken.sol';

contract GhoATokenHelper {
  GhoAToken ghoAToken;
  DummyAccessControl dummy;

  /**
   * @notice Returns a bool (=> CONSTANT)
   * @param addressNotUsed is ignored
   * @return bool  _.isPoolAdmin(address) => CONSTANT
   */
  function isPoolAdmin(address addressNotUsed) public view returns (bool) {
    return dummy.isPoolAdmin(addressNotUsed);
  }
}

contract DummyAccessControl {
  bool isAdmin;

  function isPoolAdmin(address addressNotUsed) public view returns (bool) {
    return isAdmin;
  }
}

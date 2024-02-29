pragma solidity ^0.8.0;

import {GhoAToken} from '../../src/contracts/facilitators/aave/tokens/GhoAToken.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {IACLManager} from '../../lib/aave-stk-v1-5/lib/aave-helpers/lib/aave-address-book/lib/aave-v3-core/contracts/interfaces/IACLManager.sol';

contract GhoATokenHarness is GhoAToken {
  constructor(IPool pool) GhoAToken(pool) {}

  // just in case needed
  function getBalanceFromInterest_debt(address a) external view returns (uint256) {
    return _ghoVariableDebtToken.getBalanceFromInterest(a);
  }

  function pool_address() external view returns (address) {
    return address(POOL);
  }

  function is_pool_admin(address s) external view returns (bool) {
    IACLManager aclManager = IACLManager(_addressesProvider.getACLManager());
    return aclManager.isPoolAdmin(msg.sender);
  }
}

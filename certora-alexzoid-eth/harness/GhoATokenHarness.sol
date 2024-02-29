pragma solidity ^0.8.0;

import {GhoAToken} from '../../src/contracts/facilitators/aave/tokens/GhoAToken.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {IACLManager} from '@aave/core-v3/contracts/interfaces/IACLManager.sol';

contract GhoATokenHarness is GhoAToken {
  constructor(IPool pool) GhoAToken(pool) {}

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

pragma solidity ^0.8.0;

import {GhoAToken} from '../../src/contracts/facilitators/aave/tokens/GhoAToken.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';
import {IACLManager} from '@aave/core-v3/contracts/interfaces/IACLManager.sol';

contract GhoATokenHarness is GhoAToken {
  constructor(IPool pool) GhoAToken(pool) {}

  function RESERVE_TREASURY_ADDRESS_MOCK() external view returns (address) {
    return _treasury;
  }

  function UNDERLYING_ASSET_ADDRESS_MOCK() external view returns (address) {
    return _underlyingAsset;
  }

  function getVariableDebtTokenMock() external view returns (address) {
    return address(_ghoVariableDebtToken);
  }

  function EIP712BaseId() external view returns (string memory) {
    return _EIP712BaseId();
  }

  function stringsAreEqual(string memory str1, string memory str2) external pure returns (bool b) {
    b = keccak256(abi.encodePacked(str1)) == keccak256(abi.encodePacked(str2));
  }

  function getRevisionExternal() external pure returns (uint256) {
    return getRevision();
  }

  function getLastInitializedRevision() external view returns (uint256 lastInitializedRevision) {
    assembly {
      lastInitializedRevision := sload(0)
    }
  }

  function getInitializing() external view returns (bool initializing) {
    assembly {
      initializing := sload(1)
    }
  }

  function isPoolAdmin(address account) external returns (bool) {
    IACLManager aclManager = IACLManager(_addressesProvider.getACLManager());
    return aclManager.isPoolAdmin(account);
  }

  function getPool() external returns (address) {
    return address(POOL);
  }
}

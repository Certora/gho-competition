//SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

import {ACLManager} from '@aave/core-v3/contracts/protocol/configuration/ACLManager.sol';
import {IPoolAddressesProvider} from '@aave/core-v3/contracts/interfaces/IPoolAddressesProvider.sol';

contract MockACLManager is ACLManager {
  constructor(IPoolAddressesProvider provider) ACLManager(provider) {
    //blank
  }
}

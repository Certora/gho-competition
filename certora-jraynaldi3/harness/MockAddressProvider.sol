//SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

import {PoolAddressesProvider} from '@aave/core-v3/contracts/protocol/configuration/PoolAddressesProvider.sol';

contract MockAddressProvider is PoolAddressesProvider {
  constructor(string memory marketId, address owner) PoolAddressesProvider(marketId, owner) {
    //blank
  }
}

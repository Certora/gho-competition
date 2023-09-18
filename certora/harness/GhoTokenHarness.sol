pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';

contract GhoTokenHarness is GhoToken {
  using EnumerableSet for EnumerableSet.AddressSet;

  constructor() GhoToken(msg.sender) {}

  // just in case needed and can not be implemented in the GhoTokenHelper
}

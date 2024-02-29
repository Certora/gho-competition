pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';

contract GhoTokenHarness is GhoToken {
  using EnumerableSet for EnumerableSet.AddressSet;

  constructor() GhoToken(msg.sender) {}

  function getFacilitatorBucketHarness(
    address facilitator
  ) external view returns (uint256, uint256) {
    Facilitator memory f = this.getFacilitator(facilitator);
    return (f.bucketCapacity, f.bucketLevel);
  }
}

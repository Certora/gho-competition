pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';

contract GhoTokenHelper {
  GhoToken ghoToken;

  /**
   * @notice Returns the backet capacity
   * @param facilitator The address of the facilitator
   * @return The facilitator bucket capacity
   */
  function getFacilitatorBucketCapacity(address facilitator) public view returns (uint256) {
    (uint256 bucketCapacity, ) = ghoToken.getFacilitatorBucket(facilitator);
    return bucketCapacity;
  }

  /**
   * @notice Returns the backet level
   * @param facilitator The address of the facilitator
   * @return The facilitator bucket level
   */
  function getFacilitatorBucketLevel(address facilitator) public view returns (uint256) {
    (, uint256 bucketLevel) = ghoToken.getFacilitatorBucket(facilitator);
    return bucketLevel;
  }

  /**
   * @notice Returns the length of the facilitator list
   * @return The length of the facilitator list
   */
  function getFacilitatorsListLen() external view returns (uint256) {
    address[] memory flist = ghoToken.getFacilitatorsList();
    return flist.length;
  }

  /**
   * @notice Returns the length of the facilitator list
   * @return The length of the facilitator list
   */
  function getFacilitatorsLableLen(address facilitator) external view returns (uint256) {
    return bytes(ghoToken.getFacilitator(facilitator).label).length;
  }

  /**
   * @notice Converts address to bytes32
   * @param value Some address
   * @return b the value as bytes32
   */
  function toBytes32(address value) external pure returns (bytes32 b) {
    b = bytes32(uint256(uint160(value)));
  }
}

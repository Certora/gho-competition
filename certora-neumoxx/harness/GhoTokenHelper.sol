pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';
import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';

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
   * @notice Returns the facilitator's label
   * @param facilitator The address of the facilitator
   * @return The facilitator Label
   */
  function getFacilitatorLabel(address facilitator) public view returns (string memory) {
    IGhoToken.Facilitator memory f = ghoToken.getFacilitator(facilitator);
    return f.label;
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

  /**
   * @notice Checks that two strings are equal
   * @param str1 first string
   * @param str2 second string
   * @return b true if strings are equal
   */
  function stringsAreEqual(string memory str1, string memory str2) external pure returns (bool b) {
    b = keccak256(abi.encodePacked(str1)) == keccak256(abi.encodePacked(str2));
  }
}

pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';

interface Ap {
  function getACLManager() external view returns (address);
}

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
  function getFacilitatorsLabelLen(address facilitator) external view returns (uint256) {
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

  function nullAddress() external pure returns (address) {
    return address(0);
  }

  function isPoolAdmin(address a) external returns (bool) {
    // any logic is good
    return (uint160(bytes20(a)) & 1) == 1;
  }

  function isPoolAdminSummarized(address a) external returns (bool) {
    return this.isPoolAdmin(a);
  }

  function areStringsSame(string memory a, string memory b) external returns (bool) {
    return keccak256(bytes(a)) == keccak256(bytes(b));
  }

  function compare(string memory str1, string memory str2) public pure returns (bool) {
    return keccak256(abi.encodePacked(str1)) == keccak256(abi.encodePacked(str2));
  }

  function askForACLManager(address ap) external returns (address) {
    return Ap(ap).getACLManager();
  }

  function justRevert() external {
    revert();
  }

  function balanceOf(address token, address user) external returns (uint) {
    return IGhoToken(token).balanceOf(user);
  }
}

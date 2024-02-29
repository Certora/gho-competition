pragma solidity ^0.8.0;

import {IGhoToken} from '../../src/contracts/gho/interfaces/IGhoToken.sol';
import '@openzeppelin/contracts/utils/structs/EnumerableSet.sol';
import {GhoToken} from '../../src/contracts/gho/GhoToken.sol';
import {WadRayMath} from '@aave/core-v3/contracts/protocol/libraries/math/WadRayMath.sol';
import {PercentageMath} from '@aave/core-v3/contracts/protocol/libraries/math/PercentageMath.sol';

contract GhoTokenHelper {
  using WadRayMath for uint256;
  using PercentageMath for uint256;

  GhoToken ghoToken;

  /**
   * @notice Returns the backet capacity
   * @param facilitator The address of the facilitator
   * @return The facilitator bucket capacity
   */
  function getFacilitatorBucketCapacity(address facilitator) external view returns (uint256) {
    (uint256 bucketCapacity, ) = ghoToken.getFacilitatorBucket(facilitator);
    return bucketCapacity;
  }

  /**
   * @notice Returns the backet level
   * @param facilitator The address of the facilitator
   * @return The facilitator bucket level
   */
  function getFacilitatorBucketLevel(address facilitator) external view returns (uint256) {
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

  //
  // Added functions
  //

  /**
   * @notice Check if account has FACILITATOR_MANAGER_ROLE
   * @param account Some address
   * @return true if account has FACILITATOR_MANAGER_ROLE, false othserwise
   */
  function hasFacilitatorManagerRole(address account) external view returns (bool) {
    return ghoToken.hasRole(ghoToken.FACILITATOR_MANAGER_ROLE(), account);
  }

  /**
   * @notice Check if account has BUCKET_MANAGER_ROLE
   * @param account Some address
   * @return true if account has BUCKET_MANAGER_ROLE, false othserwise
   */
  function hasBacketManagerRole(address account) external view returns (bool) {
    return ghoToken.hasRole(ghoToken.BUCKET_MANAGER_ROLE(), account);
  }

  /**
   * @notice Compare two strings
   * @param a first string
   * @param b second string
   * @return true if equal, false othserwise
   */
  function compareStrings(string memory a, string memory b) external pure returns (bool) {
    return keccak256(abi.encodePacked(a)) == keccak256(abi.encodePacked(b));
  }

  function rayMul(uint256 x, uint256 y) external view returns (uint256) {
    return x.rayMul(y);
  }

  function rayDiv(uint256 x, uint256 y) external view returns (uint256) {
    return x.rayDiv(y);
  }

  function percentMul(uint256 x, uint256 y) external view returns (uint256 result) {
    assert(y != 0);
    return x.percentMul(y);
  }
}

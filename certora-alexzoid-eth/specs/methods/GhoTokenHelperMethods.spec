using GhoTokenHelper as _GhoTokenHelper;

methods{
    
    function _GhoTokenHelper.getFacilitatorBucketCapacity(address facilitator) external returns (uint256) envfree;
    function _GhoTokenHelper.getFacilitatorBucketLevel(address facilitator) external returns (uint256) envfree;
    function _GhoTokenHelper.getFacilitatorsListLen() external returns (uint256) envfree;
    function _GhoTokenHelper.getFacilitatorsLabelLen(address facilitator) external returns (uint256) envfree;
    function _GhoTokenHelper.toBytes32(address value) external returns (bytes32) envfree;

    function _GhoTokenHelper.hasFacilitatorManagerRole(address account) external returns (bool) envfree;
    function _GhoTokenHelper.hasBacketManagerRole(address account) external returns (bool) envfree;
    function _GhoTokenHelper.compareStrings(string a, string b) external returns (bool) envfree;
    function _GhoTokenHelper.rayMul(uint256 x, uint256 y) external returns (uint256) envfree;
    function _GhoTokenHelper.rayDiv(uint256 x, uint256 y) external returns (uint256) envfree;
    function _GhoTokenHelper.percentMul(uint256 x, uint256 y) external returns (uint256) envfree;
}
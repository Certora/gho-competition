contract DummyPool {
  function getReserveNormalizedVariableDebt(address asset) external view returns (uint256) {
    return _getReserveNormalizedVariableDebtWithBlockTimestamp(asset, block.timestamp);
  }

  function _getReserveNormalizedVariableDebtWithBlockTimestamp(
    address asset,
    uint256 blockTs
  ) internal view returns (uint256) {
    assert(false); // will be replaced by a summary in the spec file
  }
}

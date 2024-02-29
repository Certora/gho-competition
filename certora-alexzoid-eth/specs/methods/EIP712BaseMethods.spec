methods{
    // EIP712Base
    function DOMAIN_SEPARATOR() internal returns (bytes32); // overridden in GhoAToken
    function nonces(address owner) internal returns (uint256); // overridden in GhoAToken
    function _calculateDomainSeparator() internal returns (bytes32);
}
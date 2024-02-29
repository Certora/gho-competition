import "ghoFlashMinter.spec";

use invariant fee_less_than_MAX_FEE;

/**
* @title proves that the fee paid cannot be smaller if the flash loan was split among many smaller loans
* Fails because the fee is not always rounded up, hence the flash borrower can pay lower fees by invoking flash loan recursively
* the opportunity loss of the protocol is bounded by the number of revirsive calls to flash loan,
* hence are usually minimal, though for low-decimals tokens and in case of their large value, the amount may be considerable
* with respect to gas paid.
* GitHub issue: https://github.com/Czar102/gho-verification/issues/2
* run failure example: https://prover.certora.com/output/2949/df8dc08d8136475aa15b51c6b784aab4/?anonymousKey=885f66099021967e0603c91ade37717fd1118438
**/
rule cantPayLowerFeeBySplitting() {
    address token;
    uint amount;
    uint t1;
    require t1 <= amount;
    uint t2 = require_uint256(amount - t1);

    requireInvariant fee_less_than_MAX_FEE();

    env e;
    assert to_mathint(flashFee(e, token, amount)) <= flashFee(e, token, t1) + flashFee(e, token, t2);
}

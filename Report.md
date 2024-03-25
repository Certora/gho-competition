## Table of contents

- [**Overview**](#overview)
    - [**About Certora**](#about-certora)
    - [**Summary**](#summary)
- [**Mutations**](#mutations)
    - [**GhoToken**](#ghotoken)
    - [**GhoAToken**](#ghoatoken)
    - [**GhoFlashMinter**](#ghoflashminter)
    - [**GhoVariableDebtToken**](#ghovariabledebttoken)
- [**Notable Properties**](#notable-properties)
    - [**GhoToken**](#ghotoken-1)
    - [**GhoAToken**](#ghoatoken-1)
    - [**GhoFlashMinter**](#ghoflashminter-1)
    - [**GhoVariableDebtToken**](#ghovariabledebttoken-1)
- [**Disclaimer**](#disclaimer)

# Overview

## About Certora

Certora is a Web3 security company that provides industry-leading formal verification tools and smart contract audits. Certora’s flagship security product, Certora Prover, is a unique SaaS product which locates hard-to-find bugs in smart contracts or mathematically proves their absence.

A formal verification contest is a competition where members of the community mathematically validate the accuracy of smart contracts, in return for a reward offered by the sponsor based on the participants' findings and property coverage.

In the formal verification contest detailed here, contenders formally verified GhoToken smart contracts. This formal verification contest was held from September 27, 2023 until October 15, 2023.

## Summary 

Mutations are used to evaluate the quality of the specification. The mutations are described below and were made available at the end of the contest, you can find them [here](https://github.com/Certora/gho-competition/tree/certora/competition/certora/mutations). Additionally, the top specifications have been added to the [contest repo](https://github.com/Certora/gho-competition/tree/certora/competition) and some specific properties have been included in this report as good examples. You can find the final results for the competition [here](https://docs.google.com/spreadsheets/d/1bOi5IYGPQTPQ9PzsqyJm81kaCkqFXC9qAcv1xtoB9_U/edit#gid=1970712821)

# Mutations

## GhoToken

[**GhoToken_1.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_1.sol): In `addFacilitator`, require `facilitatorLabel` to have length equal to 1 instead of greater than 0.

[**GhoToken_2.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_2.sol): In `setFacilitatorBucketCapacity`, remove `onlyRole(BUCKET_MANAGER_ROLE)` modifier.

[**GhoToken_3.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_3.sol): In `removeFacilitator`, require `_facilitators[facilitatorAddress].label).length` to equal 9 instead of being greater than 0.

[**GhoToken_4.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_4.sol): In `addFacilitator`, remove `onlyRole(FACILITATOR_MANAGER_ROLE)` modifier.

[**GhoToken_5.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_5.sol): In `removeFacilitator`, remove `onlyRole(FACILITATOR_MANAGER_ROLE)` modifier.

[**GhoToken_6.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_6.sol): In `setFacilitatorBucketCapacity` add `require(newCapacity == 0)`, making it impossible to increase capacity of a facilitator.

[**GhoToken_P.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoToken/GhoToken_P.sol): In `addFacilitator`, set `facilitator.bucketCapacity` to 0 instead of the inputted value `bucketCapacity`.

## GhoAToken

[**GhoAToken_0.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_0.sol): In `setVariableDebtToken`, remove `onlyPoolAdmin` modifier.

[**GhoAToken_1.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_1.sol): In `distributeFeesToTreasury` transfer amount `1` instead of `balance`.

[**GhoAToken_2.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_2.sol): Remove functionality from `rescueTokens`.

[**GhoAToken_3.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_3.sol): In `transferUnderlyingTo`, mint `amount + 1 ether` instead of `amount`.

[**GhoAToken_4.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_4.sol): In `handleRepayment`, mutate if boolean from `<=` to `<` to lead to a DoS in the equal case.

[**GhoAToken_5.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_5.sol): In `updateGhoTreasury`, replace '!=' with '==', requiring `newGhoTreasury` to be 0.

[**GhoAToken_6.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_6.sol): In `setVariableDebtToken`, replace `!=` with `==`, causing `_ghoVariableDebtToken` to always be 0.

[**GhoAToken_7.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_7.sol): In `transferUnderlyingTo`, replace `amount` with `0`.

[**GhoAToken_8.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_8.sol): In `handleRepayment`, replace `<=` with `>`, making it impossible to repay more than interest.

[**GhoAToken_P.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoAToken/GhoAToken_P.sol): In `handleRepayment`, remove balance decrease functionality when repaying more than interest.

## GhoFlashMinter

[**GhoFlashMinter_0.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_0.sol): In `constructor`, remove the max free check.

[**GhoFlashMinter_1.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_1.sol): Change `MAX_FEE` value from 1e4 to 1e20, effectively removing the cap on fee.

[**GhoFlashMinter_2.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_2.sol): In `_updateFee`, remove the max fee check.

[**GhoFlashMinter_3.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_3.sol): Change `MAX_FEE` value from `1e4` to `1`, effectively removing fee functionality.

[**GhoFlashMinter_4.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_4.sol): In `constructor`, don't call `_updateGhoTreasury` and `updateFee`, leaving the relevant values at 0.

[**GhoFlashMinter_5.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_5.sol): In `constructor`, swap `ghoTreasury` and `ghoToken` incorrectly initializing the values.

[**GhoFlashMinter_6.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_6.sol): In `onlyPoolAdmin` modifier, replace check with a check that caller is `address(100)`.

[**GhoFlashMinter_7.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_7.sol): In `flashLoan`, fail to mint new tokens to receiver.

[**GhoFlashMinter_P.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoFlashMinter/GhoFlashMinter_P.sol): Remove functionality from `onlyPoolAdmin` modifier. 

## GhoVariableDebtToken

[**GhoVariableDebtToken_0.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_0.sol): In `_burnScaled`, fail to burn in the case where `amount == balanceBeforeBurn`.

[**GhoVariableDebtToken_1.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_1.sol): In `updateDiscountDistribution`, multiply the total normalized variable debt by 2.

[**GhoVariableDebtToken_2.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_2.sol): In `mint`, always decrease allowance, requiring users to always approve their own tokens.

[**GhoVariableDebtToken_3.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_3.sol): In `mint`, change `if(user != onBehalfOf)` to `require(user != onBehalfOf)`, making it impossible to borrow on behalf of another user.

[**GhoVariableDebtToken_4.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_4.sol): In `setAToken`, change `!=` to `==`, making it impossible to set an aToken.

[**GhoVariableDebtToken_5.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_5.sol): In `updateDiscountDistribution`, fail to apply discount to the user.

[**GhoVariableDebtToken_6.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_6.sol): In `updateDiscountRateStrategy`, fail to update `_discountRateStrategy`, making it always 0.

[**GhoVariableDebtToken_7.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_7.sol): In `updateDiscountToken`, remove `onlyPoolAdmin` modifier.

[**GhoVariableDebtToken_8.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_8.sol): In `_accrueDebtOnAction`, replace user's `accumulatedDebtInterest` with `balanceIncrease` instead of adding it on. 

[**GhoVariableDebtToken_9.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_9.sol): In `updateDiscountDistribution`, remove `_burn` call when `recipientPreviousScaledBalance > 0`, failing to apply discount to recipient.

[**GhoVariableDebtToken_10.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_10.sol): In `_burnScaled`, burn `amountScaled` instead of `amountScaled + discountScaled`.

[**GhoVariableDebtToken_11.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_11.sol): In `_accrueDebtOnAction`, fail to update `discountScaled`, making it always equal to 0.

[**GhoVariableDebtToken_12.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_12.sol): In `_mintScaled`, when `amountScaled > discountScaled`, add discount to debt instead of subtracting it.

[**GhoVariableDebtToken_13.sol**](https://github.com/Certora/gho-competition/blob/certora/competition/certora/mutations/GhoVariableDebtToken/GhoVariableDebtToken_13.sol): In `updateDiscountDistribution`, when `senderPreviousScaledBalance > 0`, fail to decrement discount token balance, enabling users to remove all debt. 

# Notable Properties 

## GhoToken

A final GhoToken spec was compiled using the best specs from this competition. It can be found [here.](https://github.com/Certora/gho-competition/blob/certora/competition/certora/specs/ghoToken.spec)

## GhoAToken

### Two calls of `handleRepayment` must be equivalent to one call if the sum of two amounts is equal to the one.

*Author:* [0xpoolboy](https://github.com/Certora/gho-competition/blob/certora/competition/certora-0xpoolboy/specs/ghoAToken.spec#L415-L438)

```
rule linearityOfHandleRepayment(
	env e,
	address user,
	address onBehalfOf,
	uint256 amount1,
	uint256 amount2
) {
	mathint balanceFromInterestBefore = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);
	mathint levelBefore = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);

	storage initState = lastStorage;

	handleRepayment(e, user, onBehalfOf, require_uint256(amount1));
	handleRepayment(e, user, onBehalfOf, require_uint256(amount2));
	mathint levelAfter_2 = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter_2 = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	handleRepayment(e, user, onBehalfOf, require_uint256(amount1+amount2)) at initState;
	mathint levelAfter_1 = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint balanceFromInterestAfter_1 = GhoVariableDebtToken.getBalanceFromInterest(e, onBehalfOf);

	assert levelAfter_2 == levelAfter_1;
	assert balanceFromInterestAfter_2 == balanceFromInterestAfter_1;
}
```

---

### GhoAToken's `bucketLevel` must be change when calling `mint` and `burn`.

*Author:* [alexzoid-eth](https://github.com/Certora/gho-competition/blob/certora/competition/certora-alexzoid-eth/specs/ghoAToken.spec#L566-L582)

```
rule possibilityOfBurnMintChangeBucketLevel(env e, method f, calldataarg args) 
    filtered { f -> BURN_MINT_USE_FUNCTIONS(f) } {

    require(e.msg.sender == getPoolAddress());

    uint256 bucketLevelBefore = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);
    require(bucketLevelBefore != 0);

    uint256 bucketCapacityBefore = _GhoTokenHelper.getFacilitatorBucketCapacity(e, currentContract);
    require(bucketCapacityBefore > bucketLevelBefore);

    f(e, args);
    
    uint256 bucketLevelAfter = _GhoTokenHelper.getFacilitatorBucketLevel(e, currentContract);

    satisfy(bucketLevelAfter != bucketLevelBefore);
}
```

---

### Variables `ghoTreasury` and `ghoVariableDebtToken` must not be updated to zero.

*Author:* [alexzoid-eth](https://github.com/Certora/gho-competition/blob/certora/competition/certora-alexzoid-eth/specs/ghoAToken.spec#L400-L411)

```
rule systemVariablesNotSetToZero(env e, method f, calldataarg args) 
    filtered { f -> !VIEW_FUNCTIONS(f) && !INITIALIZE_FUNCTION(f) } {

    require(ghostGhoTreasuryWritten == false);
    require(ghostGhoVariableDebtTokenWritten == false);

    f@withrevert(e, args);
    bool reverted = lastReverted;

    assert(!reverted && ghostGhoTreasuryWritten => ghostGhoTreasury != 0);
    assert(!reverted && ghostGhoVariableDebtTokenWritten => ghostGhoVariableDebtToken != 0);
}
```

---

### State change and revert reasons of the `transferUnderlyingTo` must work are as intended.

*Author:* [Czar102](https://github.com/Certora/gho-competition/blob/certora/competition/certora-Czar102/specs/ghoAToken.spec#L352-L378)

```
rule transferUnderlyingToIntegrity() {
	env e;
	address to;
	uint amount;
	bool isPool = (e.msg.sender == POOL());
	uint level = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	uint capacity = GhoTokenHelper.getFacilitatorBucketCapacity(currentContract);

	uint balanceOfBefore = GHOTOKEN.balanceOf(to);
	require balanceOfBefore + amount <= max_uint256;

	require (GHOTOKEN.totalSupply() + amount) <= max_uint256;

	transferUnderlyingTo@withrevert(e, to, amount);
	bool reverted = lastReverted;

	assert reverted <=> (
		amount + level > to_mathint(capacity) ||
		!isPool ||
		amount == 0 ||
		e.msg.value != 0
	);

	assert !reverted => (
		to_mathint(GHOTOKEN.balanceOf(to)) == balanceOfBefore + amount
	);
}
```

--- 

### State change and revert reasons of the `handleRepayment` must work are as intended.

*Author:* [neumoxx](https://github.com/Certora/gho-competition/blob/certora/competition/certora-neumoxx/specs/ghoAToken.spec#L425-L454)

```
rule handleRepaymentConsistencyCheck(env e) {

	address user;
    address onBehalfOf;
    uint256 amount;

	uint256 balancePre = GHOTOKEN.balanceOf(e, currentContract);
	uint256 balanceFromInterestPre = GHOVARDEBTOKEN.getBalanceFromInterest(e, onBehalfOf);
	uint256 preTotalSupply = GHOTOKEN.totalSupply(e);
	mathint facilitatorLevel = GhoTokenHelper.getFacilitatorBucketLevel(currentContract);
	mathint finalBalanceFromInterest = (balanceFromInterestPre - amount) < 0?0:(balanceFromInterestPre - amount);

    handleRepayment@withrevert(e, user, onBehalfOf, amount);
    bool lastRev = lastReverted;

	uint256 balanceFromInterestPost = GHOVARDEBTOKEN.getBalanceFromInterest(e, onBehalfOf);
	uint256 postTotalSupply = GHOTOKEN.totalSupply(e);

    assert lastRev <=>  (
		e.msg.value > 0 ||
		getPool(e) != e.msg.sender || 
		(amount > balanceFromInterestPre && facilitatorLevel < (amount - balanceFromInterestPre)) ||
		(amount > balanceFromInterestPre && to_mathint(balancePre) < (amount - balanceFromInterestPre)) ||
		finalBalanceFromInterest < 0
	);
    assert !lastRev => (
		balanceFromInterestPost == assert_uint256(finalBalanceFromInterest) &&
		(amount > balanceFromInterestPre => postTotalSupply == require_uint256(preTotalSupply - (amount - balanceFromInterestPre)))
	);
}
```

---

## GhoFlashMinter

### Total amount loaned by `flashLoan` must not exceed `maxFlashLoan`.

*Author:* [0xpoolboy](https://github.com/Certora/gho-competition/blob/certora/competition/certora-0xpoolboy/specs/ghoFlashMinter.spec#L244-L264)

```
rule userCannotExceedMaxAmountLoaned(address receiver, address token, uint256 amount, bytes data)
{
    env e;

    uint256 ghoLevel; uint256 ghoCapacity;
    ghoCapacity, ghoLevel = gho.getFacilitatorBucket(e, currentContract);
    require ghoLevel <= ghoCapacity;

    // Set the mock-contracts helper variables to zero.
    require flashBorrower.accumulatedAmount(e) == 0;

    flashLoanReqs(e);

    mathint maxAmount = maxFlashLoan(e, token);

    flashLoan(e, receiver, token, amount, data);

    mathint totalAmount = flashBorrower.accumulatedAmount(e);

    assert totalAmount <= maxAmount;
}
```

---

### `_fee` must not be greater than `MAX_FEE`.

*Author:* [alexzoid-eth](https://github.com/Certora/gho-competition/blob/certora/competition/certora-alexzoid-eth/specs/ghoFlashMinter.spec#L285-L286)

```
invariant feeLessThanOrEqualToMax() 
    ghostFee <= MAX_FEE() 
    filtered { f -> !VIEW_FUNCTIONS(f) }
```

---

### `bucketLevel` must be zero.

*Author:* [Czar102](https://github.com/Certora/gho-competition/blob/certora/competition/certora-Czar102/specs/ghoFlashMinter.spec#L351-L357)

```
invariant debt_stays_zero()
	GhoTokenHelper.getFacilitatorBucketLevel(currentContract) == 0
	{
		preserved {
			require careAboutParamChanges == false;
		}
	}
```

---

### Variables `_ghoTreasury` and `_fee` must only be updatable by pool admin.

*Author:* [himanshu-Bhatt](https://github.com/Certora/gho-competition/blob/certora/competition/certora-himanshu-Bhatt/specs/ghoFlashMinter.spec#L188-L196)

```
rule onlyPoolAdminCanUpdateFeeTreasury(method f, env e, calldataarg args) {
    uint256 _fee; address _treasury; uint256 fee_; address treasury_;
    _fee=getFee(e);
    _treasury=getGhoTreasury(e);
    
    f(e,args);
    
    fee_=getFee(e);
    treasury_=getGhoTreasury(e);
    
    assert _fee != fee_ || _treasury != treasury_ => retreivePoolAdminFromGhost(e.msg.sender) == true;
}
```

---

### `flashLoan` must not change `totalSupply`.

*Author:* [jraynaldi3](https://github.com/Certora/gho-competition/blob/certora/competition/certora-jraynaldi3/specs/ghoFlashMinter.spec#L240-L250)

```
rule totalSupply_monoton(env e, method f, calldataarg args) {
    mathint action = assert_uint256(flashBorrower.action());
    uint256 supplyBefore = gho.totalSupply();

    f(e,args);
    
    uint256 supplyAfter = gho.totalSupply();
    assert action != 4 && action != 5 => supplyAfter == supplyBefore; 
}
```

---

## GhoVariableDebtToken

### The last stored `index` for a user must be greater than or equal to `RAY` and less than or equal to the current `index`.

*Author:* [alexzoid-eth](https://github.com/Certora/gho-competition/blob/certora/competition/certora-alexzoid-eth/specs/ghoVariableDebtToken.spec#L842-L857)

```
invariant userIndexSetup(env eInv, address user) 
    ghostUserStateAdditionalData[user] >= RAY() && ghostUserStateAdditionalData[user] <= index_ghost[eInv.block.timestamp]
    filtered { f -> !EXCLUDED_FUNCTIONS(f) } 
    {
        preserved with (env eFunc) {
            // Use the same timestamp in env and invariantEnv
            require(eInv.block.timestamp == eFunc.block.timestamp);
        }
        preserved mint(address _user, address onBehalfOf, uint256 amount, uint256 index) with (env eMint) {
            // Mint is executed with the actual index
            require(index == index_ghost[eInv.block.timestamp]);
        }
        preserved burn(address from, uint256 amount, uint256 index) with (env eBurn) {
            // Burn is executed with the actual index
            require(index == index_ghost[eInv.block.timestamp]);
        }
    }
```

---

### Updated value of `discountPercent` must be different from the old value.

*Author:* [alexzoid-eth](https://github.com/Certora/gho-competition/blob/certora/competition/certora-alexzoid-eth/specs/ghoVariableDebtToken.spec#L1151-L1153)

```
invariant discountPercentChangedToDifferentValue(address user) 
    ghostDiscountPercentWritten[user] => ghostDiscountPercentPrev[user] != ghostDiscountPercent[user]
    filtered { f -> !EXCLUDED_FUNCTIONS(f) }
```

---

### A user's balance must be less than or equal to calculated balance.

*Author:* [himanshu-Bhatt](https://github.com/Certora/gho-competition/blob/certora/competition/certora-himanshu-Bhatt/specs/ghoVariableDebtToken.spec#L401-L407)

```
rule balanceOf_lessThanEqual_scaledBalance_X_index(method f, calldataarg args, env e) 
    filtered {f -> !f.isView && !disAllowedFunctions(f)} {

	address user;
	uint256 index = indexAtTimestamp(e.block.timestamp);
    
	require(balanceOf(e,user) <= rayMul(e,scaledBalanceOf(user),index));

	f(e,args);

	assert balanceOf(e,user) <= rayMul(e,scaledBalanceOf(user),index);
}
```

---

# Disclaimer

The Certora Prover takes a contract and a specification as input and formally proves that the contract satisfies the specification in all scenarios. Notably, the guarantees of the Certora Prover are scoped to the provided specification and the Certora Prover does not check any cases not covered by the specification. 

Certora does not provide a warranty of any kind, explicit or implied. The contents of this report should not be construed as a complete guarantee that the contract is secure in all dimensions. In no event shall Certora or any of its employees or community participants be liable for any claim, damages, or other liability, whether in an action of contract, tort, or otherwise, arising from, out of, or in connection with the results reported here. All smart contract software should be used at the sole risk and responsibility of users.


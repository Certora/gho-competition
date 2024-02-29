# GhoFlashMinter

## High-Level

- `availableLiquidityDoesntChange`
  - Checks that the available liquidity, retrieved by maxFlashLoan, stays the same after any action
- `integrityOfDistributeFeesToTreasury`
  - Checks the integrity of distributeFees

---

- `onlyPoolAdminCouldSetSystemVariables`
  - Only pool admin could set system variables
- `flashLoanShouldIncreaseBalanceByFee`
  - Flash loan should increase current contract's GHO balance
- `flashLoanShouldNotChangeOtherUserBalances`
  - No other user address balance should change

## Valid States

- `functionsNotRevert`
  - Possibility should not revert
- `feeLessThanOrEqualToMax`
  - Fee could not be greater than MAX_FEE
- `possibilityMaxFlashLoanGTZero`
  - Possibility maxFlashLoan greater than zero for GhoToken

## State Transitions

- `onFlashLoanCallbackInitiatorIntegrity`
  - onFlashLoan callback integrity

## Variable Transitions

- `possibilityFeeSetToMax`
  - Fee could be set to MAX_FEE

## Unit Tests

- `integrityOfTreasurySet`
  - Checks the integrity of updateGhoTreasury - after update the given address is set
- `integrityOfFeeSet`
  - Checks the integrity of updateFee - after update the given value is set

---

- `functionsNotRevert`
  - Possibility should not revert
- `viewersIntegrity`
  - Viewer functions integrity
- `flashFeeRevertsWhenNotGhoToken`
  - flashFee() reverts when not GHO token
- `flashLoanOnlyGhoTokensSupported`
  - Flashloan supports only GHO tokens

# GhoVariableDebtToken

## High-Level

- `debtTokenIsNotTransferable`
  - Proves that debt tokens aren't transferable
- `integrityOfMint_userIsolation`
  - Proves that mint can't effect other user's scaled balance
- `integrityOfBurn_userIsolation`
  - Proves that burn can't effect other user's scaled balance
- `integrityOfUpdateDiscountDistribution_userIsolation`
  - Proves that updateDiscountDistribution can't effect other user's scaled balance
- `integrityOfRebalanceUserDiscountPercent_userIsolation`
  - Proves that rebalanceUserDiscountPercent can't effect other user's scaled balance

---

- `onlyATokenCouldDecreaseAccumulatedDebtInterest`
  - Only aToken could decrease accumulatedDebtInterest
- `onlyDiscountTokenCouldUpdateDiscountDistribution`
  - Only discount token could update discount distribution
- `discountPercentMattersInBalanceOf`
  - Discount percent matters in balanceOf()
- `discountPercentDoesNotMatterWhenUserIndexEqCurrentIndex`
  - Discount percent doesn't matters in balanceOf() when user index equal to current index
- `burnAllUserBalanceBurnAllScaledBalance`
  - Burn all user balance will burn all scaled balance

## Valid States

- `discountCantExceed100Percent`
  - At any point in time, the user's discount rate isn't larger than 100%
- `integrityOfBalanceOf_fullDiscount`
  - Proves that a user with 100% discounts has a fixed balance over time
- `integrityOfBalanceOf_noDiscount`
  - Proves that a user's balance, with no discount, is equal to rayMul(scaledBalance, current index)
- `integrityOfBalanceOf_zeroScaledBalance`
  - Proves the a user with zero scaled balance has a zero balance

---

- `userIndexSetup`
  - User_index >= RAY() and user_index <= current_index
- `delegatorCannotDecreaseSelfBorrowAllowances`
  - Delegator and delegatee could not be the same

## State Transitions

- `nonMintFunctionCantIncreaseBalance`
  - Proves that the user's balance of debt token can't increase by calling any external non-mint function.
- `nonMintFunctionCantIncreaseScaledBalance`
  - Proves that a call to a non-mint operation won't increase the user's balance of the actual debt tokens (i.e. it's scaled balance)
- `onlyCertainFunctionsCanModifyScaledBalance`
  - Proves that only burn/mint/rebalanceUserDiscountPercent/updateDiscountDistribution can modify user's scaled balance
- `userAccumulatedDebtInterestWontDecrease`
  - Proves that only a call to decreaseBalanceFromInterest will decrease the user's accumulated interest listing
- `userCantNullifyItsDebt`
  - Proves that a user can't nullify its debt without calling burn
- `onlyMintForUserCanIncreaseUsersBalance`
  - Proves that when calling mint, the user's balance will increase if the call is made on bahalf of the user
- `integrityOfBurn_fullRepay_concrete`
  - Proves a concrete case of repaying the full debt that ends with a zero balance

---

- `balanceOfZeroWhenScaledBalanceZero`
  - balanceOf() equal to zero when scaled balance is zero
- `zeroDiscountPercentNotAffectBalanceOf`
  - Zero discount percent does not affect balance
- `possibilityBurnDecreaseUserBalance`
  - Burn could decrease user balance

## Variable Transitions

- `integrityOfMint_updateIndex`
  - Proves the after calling mint, the user's state is updated with the recent index value
- `integrityOfBurn_updateIndex`
  - Proves the after calling burn, the user's state is updated with the recent index value
- `integrityOfMint_updateDiscountRate`
  - Proves that after calling mint, the user's discount rate is up to date
- `integrityOfBurn_updateDiscountRate`
  - Proves that after calling burn, the user's discount rate is up to date

---

- `initializeCouldBeExecutedOnce`
  - Initialize could be executed once
- `initializedWithSpecificPoolAddressOnly`
  - Could be initialized with specific pool address only
- `setSystemVariablesRequirements`
  - Set system variables requirements
- `possibilityGhoATokenModify`
  - GhoAToken could be modified
- `possibilityDiscountRateStrategyModify`
  - DiscountRateStrategy could be modified
- `possibilityDiscountTokenModify`
  - DiscountToken could be modified
- `discountPercentChangedToDifferentValue`
  - Discount percent changed to different value

## Unit Tests

- `disallowedFunctionalities`
  - Ensuring that the defined disallowed functions revert in any case (from VariableDebtToken.spec)
- `integrityOfMint_updateScaledBalance_fixedIndex`
  - Proves that on a fixed index calling mint(user, amount) will increase the user's scaled balance by amount
- `integrityMint_atoken`
  - Checking atoken alone (from VariableDebtToken.spec)
- `burnZeroDoesntChangeBalance`
  - Proves that calling burn with 0 amount doesn't change the user's balance (from VariableDebtToken.spec)
- `integrityOfUpdateDiscountDistribution_updateIndex`
  - Proves the after calling updateDiscountDistribution, the user's state is updated with the recent index value
- `integrityOfRebalanceUserDiscountPercent_updateDiscountRate`
  - Proves that after calling rebalanceUserDiscountPercent, the user's discount rate is up to date
- `integrityOfRebalanceUserDiscountPercent_updateIndex`
  - Proves that after calling rebalanceUserDiscountPercent, the user's state is updated with the recent index value
- `burnAllDebtReturnsZeroDebt`
  - Proves the balance will be zero when burn whole dept

---

- `initializeSetInitialParamsCorrectly`
  - Initialize set initial params correctly
- `domainSeparatorDepensOnName`
  - Domain separator depends on token name
- `viewersIntegrity`
  - Viewers integrity
- `functionsNotRevert`
  - Possibility should not revert
- `decreaseBalanceFromInterestIntegrity`
  - decreaseBalanceFromInterest() should decrease accumulated debt interest
- `rebalanceUserDiscountPercentUpdateUserIndex`
  - rebalanceUserDiscountPercent() should update user index
- `zeroDiscountPercentInBalanceOfIntegritry`
  - Zero discount percent integrity

# GhoAToken

## High-Level

- `transferUnderlyingToCantExceedCapacity`
  - Proves that calling ghoAToken::transferUnderlyingTo will revert if the amount exceeds the excess capacity
- `integrityTransferUnderlyingToWithHandleRepayment`
  - BucketLevel decreases after transferUnderlyingTo() followed by handleRepayment()

---

- `onlyPoolAdminCouldTransferOutTokens`
  - Stuck tokens could be rescued only by pool admin
- `possibilityOfRescueStuckToken`
  - Possibility of rescue stuck tokens
- `ghoTokensCouldBeTransferredOutToGhoTresauryOnly`
  - GHO tokens should be sent to ghoTresaury only. Pool admin could not rug pool GHO tokens via rescue mechanism
- `onlyPoolCanInitializeCommunicationWithGHOToken`
  - Only Pool could initialize a communication with GhoToken contract

## Valid States

- `totalSupplyAlwaysZero`
  - Proves that the total supply of GhoAToken is always zero
- `userBalanceAlwaysZero`
  - Proves that any user's balance of GhoAToken is always zero

---

- `initializeCouldBeExecutedOnce`
  - Initialize could be executed once

## State Transitions

- `possibilityOfTransferOutGhoTokensToTresaury`
  - Possibility of anyone to withdraw GHO tokens to the GHO Tresaury
- `possibilityOfBurnMintChangeBucketLevel`
  - Possibility of change current contract's bucketLevel with mint and burn
- `noAnotherUserBucketLevelCouldBeChanged`
  - Only bucketLevel of current contract could be changed
- `possibilityDecreaseWholeBalance`
  - Possibility of decrease whole balance of sGHO tokens
- `handleRepaymentBurnAnythingMoreBalanceFromInterest`
  - handleRepayment() should burn anything more than balance from interest

## Variable Transitions

- `initializedWithSpecificPoolAddressOnly`
  - Could be initialized with specific pool address only
- `onlyPoolAdminCouldUpdateCriticalAddresses`
  - Only Pool admin could set Treasury, VariableDebtToken, IncentivesController (expect in `initialize()`)
- `variableDebtTokenSetOnlyOnce`
  - VariableDebtToken could be set once
- `systemVariablesNotSetToZero`
  - System variables (ghoTreasury, ghoVariableDebtToken) could not be set to zero (expect in `initialize()`)
- `possibilityGhoTreasuryModify`
  - GhoTreasury could be modified
- `possibilityGhoVariableDebtTokenModify`
  - GhoVariableDebtToken could be modified

## Unit Tests

- `noMint`
  - Proves that ghoAToken::mint always reverts
- `noBurn`
  - Proves that ghoAToken::burn always reverts
- `noTransfer`
  - Proves that ghoAToken::transfer always reverts

---

- `initializeSetInitialParamsCorrectly`
  - Initialize set initial params correctly
- `specificFunctionsAlwaysRevert`
  - Specific functions always reverts
- `viewersIntegrity`
  - Viewers integrity
- `domainSeparatorDepensOnName`
  - Domain separator depends on token name
- `functionsNotRevert`
  - Possibility should not revert

# GhoToken

## High-Level

- `facilitatorInListAfterMintAndBurn`
  - [5] Facilitator is valid after successful call to `mint()` or `burn()`
- `mintLimitedByFacilitatorRemainingCapacity`
  - Proves that you can't mint more than the facilitator's remaining capacity
- `burnLimitedByFacilitatorLevel`
  - Proves that you can't burn more than the facilitator's current level

---

- `onlyFacilitatorManagerCouldModifyFacilitatorList`
  - Only account with `FACILITATOR_MANAGER_ROLE` can add or remove facilitators
- `onlyBucketManagerCouldModifyBucketCapacity`
  - Only account with `BUCKET_MANAGER_ROLE` can modify bucketCapacity

## Valid States

- `sumAllBalance_eq_totalSupply`
  - Sum of balances is `totalSupply()`
- `inv_balanceOf_leq_totalSupply`
  - User's balance not greater than `totalSupply()`
- `total_supply_eq_sumAllLevel`
  - Sum of bucket levels is equals to `totalSupply()`
- `sumAllLevel_eq_sumAllBalance`
  - The sum of bucket level is equal to the sum of GhoToken balances
- `inv_valid_capacity`
  - A facilitator with a positive bucket capacity exists in the `_facilitators` mapping
- `inv_valid_level`
  - A facilitator with a positive bucket level exists in the `_facilitators` mapping
- `level_leq_capacity`
  - Bucket level <= bucket capacity unless `setFacilitatorBucketCapacity()` lowered it

---

- `facilitatorShouldNotAddedTwice`
  - Couln't add the same (with the same label) facilitator twice
- `facilitatorAddedWithEmptyLabelShouldRevert`
  - Couln't add facilitator with empty label
- `removeFacilitatorShouldEmptyLabel`
  - Facilitator's label empty after been removed

## State Transitions

- `mint_after_burn`
  - If Bucket level < bucket capacity then the first invocation of `mint()` succeeds after `burn()`
- `burn_after_mint`
  - Burn after mint succeeds
- `level_unchanged_after_mint_followed_by_burn`
  - BucketLevel remains unchanged after `mint()` followed by `burn()`
- `level_after_mint`
  - BucketLevel changed correctly after `mint()`
- `level_after_burn`
  - BucketLevel changed correctly after `burn()`
- `address_not_in_list_after_removeFacilitator`
  - Facilitator address is removed from list (GhoToken.\_facilitatorsList.\_values) after calling `removeFacilitator`
- `balance_after_mint`
  - Balance changed correctly after `mint()`
- `balance_after_burn`
  - Balance changed correctly after `burn()`

---

- `mintBurnAffectOnlySenderFacilitator`
  - Mint and burn affect only sender's facilitator
- `onlyExistingFacilitatorCouldBeRemovedOrSetBucketCapacity`
  - Only existing facilitator could be removed or set bucket capacity

## Variable Transitions

---

- `addFacilitatorShouldSetLabelAndBucketCapacity`
  - addFacilitator() set label and bucket capacity
- `onlyFacilitatorWithZeroBucketLevelCouldBeRemoved`
  - Only facilitator with zero bucketLevel could be removed

## Unit Tests

- `facilitator_in_list_after_setFacilitatorBucketCapacity`
  - Facilitator is valid after successful call to setFacilitatorBucketCapacity()
- `getFacilitatorBucketCapacity_after_setFacilitatorBucketCapacity`
  - GhoTokenHelper.getFacilitatorBucketCapacity() called after setFacilitatorBucketCapacity() return the assign bucket capacity
- `facilitator_in_list_after_addFacilitator`
  - Facilitator is valid after successful call to `addFacilitator()`
- `mintBurnShouldRevertWhenZeroAmount`
  - Mint and burn revert when amount is zero

---

- `gettersIntegrity`
  - Prove view function work as expected
- `functionsNotRevert`
  - Possibility should not revert

## Setup

- `facilitatorsList_setInvariant`
  - `EnumerableSet.AddressSet` internal coherency
- `addr_in_set_iff_in_map`
  - `Facilitator.label` <=> `EnumerableSet.AddressSet` (`_indexes[value]`) coherency
- `valid_facilitatorLabel`
  - `Facilitator.label` <=> `ghoToken.getFacilitator(facilitator).label` coherency

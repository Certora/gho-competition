pragma solidity ^0.8.0;

import {GhoAToken} from '../../src/contracts/facilitators/aave/tokens/GhoAToken.sol';
import {IPool} from '@aave/core-v3/contracts/interfaces/IPool.sol';

contract GhoATokenHarness is GhoAToken {
  constructor(IPool pool) GhoAToken(pool) {}

  // just in case needed
}

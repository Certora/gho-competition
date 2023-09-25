using DummyERC20WithTimedBalanceOf as WTF;
methods {
		function WTF.balanceOf(address user) external returns (uint256) with (env e) => balanceOfDiscountTokenAtTimestamp(user, e.block.timestamp) ;
}


ghost mapping(address => mapping (uint256 => uint256)) discount_ghost;

/**
* Query discount_ghost for the [user]'s balance of discount token at [timestamp]
**/
function balanceOfDiscountTokenAtTimestamp(address user, uint256 timestamp) returns uint256 {
	return discount_ghost[user][timestamp];
}


rule sanity() {
	calldataarg args;
	env e;
	mint(e,args);
	assert false; 
}

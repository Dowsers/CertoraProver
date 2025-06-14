/**
 * # ERC20 Example
 *
 * This is an example specification for a generic ERC20 contract. It contains several
 * simple rules verifying the integrity of the transfer function.
 * To run, execute the following command in terminal:
 *
 * certoraRun ERC20.sol --verify ERC20:ERC20.spec --solc solc8.0
 *
 * One of the rules here is badly phrased, and results in an erroneous fail.
 * Understand the counter example provided by the Prover and then run the fixed
 * spec:
 *
 * certoraRun ERC20.sol --verify ERC20:ERC20Fixed.spec --solc solc8.0
 */

// The methods block below gives various declarations regarding solidity methods.
methods
{
    // When a function is not using the environment (e.g., `msg.sender`), it can be
    // declared as `envfree`
    function balanceOf(address) external returns (uint) envfree;
    function allowance(address,address) external returns(uint) envfree;
    function totalSupply() external returns (uint) envfree;
    function transfer(address,uint256) external returns bool envfree;
    function transferFrom(address,address,uint256) external returns bool envfree;
    function approve(address,uint256) external returns bool;
}



/**
 * @id ERC20_BASE_001
 * @dev Total supply should change only by means of mint or burn
 * @language CVL
 */
rule ERC20_BASE_001(method f) {
	env e;

	uint256 totalSupplyBefore = totalSupply();
	calldataarg args;
	f(e,args);

	assert totalSupply() == totalSupplyBefore, "Total supply changed without mint or burn";

	assert (
		totalSupply() == totalSupplyBefore,
		"Total supply changed without mint, burn or burnFrom");
}



// Rule: Each user's balance must not exceed the total supply XXXX
// invariant ERC20_BASE_002(address user)
//     balanceOf(user) <= totalSupply();

/**
 * @id ERC20_BASE_002
 * @dev Each user's balance must not exceed the total supply
 * @language CVL
 */
rule ERC20_BASE_002() {
    env e;
    method f;
    calldataarg args;

    require e.msg.sender != 0;

    uint256 balance_before = balanceOf(e.msg.sender);
    uint256 totalSupply_before = totalSupply();

    require totalSupply_before >= balance_before;

	f(e,args);

    assert totalSupply() >= balanceOf(e.msg.sender), "msg.sender balance higher than total supply";
}


// Rule: Sum of specified user balances must not exceed total supply
ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

hook Sstore _balances[KEY address user] uint256 newBalance (uint256 oldBalance)
{
    // there is no `+=` operator in CVL
    sumBalances = sumBalances + newBalance - oldBalance;
}

invariant ERC20_BASE_003()
    to_mathint(totalSupply()) == sumBalances;

// rule ERC20_BASE_003() {
//     env e;
       // Define the addresses of specific users to check
//     address everyUser1;
//     address everyUser2;
//     address everyUser3;
//     uint256 totalUserBalances = balanceOf(everyUser1) + balanceOf(everyUser2) + balanceOf(everyUser3);
       // Ensure that the sum of user balances does not exceed the total supply
//     assert totalUserBalances <= totalSupply(), "Sum of user balances higher than total supply";
// }


// Rule: Address zero should have zero balance
invariant ERC20_BASE_004()
    to_mathint(balanceOf(0)) == 0;


/**
 * @id ERC20_BASE_005
 * @dev Transfers to the zero address should not be allowed
 * @language CVL
 */
rule ERC20_BASE_005(env e) {
	uint256 amount = balanceOf(e.msg.sender);
	bool res = transfer@withrevert(e, 0, amount);
    assert lastReverted || !res, "Transfer to address zero did not revert or succeeded unexpectedly";
}


/**
 * @id ERC20_BASE_006
 * @dev Transfers to zero address should not be allowed
 * @language CVL
 */
rule ERC20_BASE_006(env e, uint256 value) {
	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 curr_allowance = allowance(e, e.msg.sender, currentContract);
	uint256 maxValue = balance_sender >= curr_allowance ? curr_allowance : balance_sender;

    require value <= curr_allowance  && value <= balance_sender;

	bool res = transferFrom@withrevert(e, e.msg.sender, 0, value);
    assert lastReverted || !res, "Transfer to address zero did not revert or succeeded unexpectedly";
}


/**
 * @id ERC20_BASE_007
 * @dev Self transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_007(uint256 value){
	env e;
	uint256 balance_sender = balanceOf(e.msg.sender);

    require e.msg.sender != 0;
	require balance_sender > 0;
    require value <= balance_sender;

	bool res = transfer(e, e.msg.sender, value);

	assert res, "Failed self transfer";
	assert balance_sender == balanceOf(e.msg.sender), "Self transfer breaks accounting";
}




/**
 * @id ERC20_BASE_008
 * @dev Self transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_008(uint256 value){
	env e;
	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 curr_allowance = allowance(e,e.msg.sender, currentContract);

    require e.msg.sender != 0;
	require balance_sender > 0 && curr_allowance > 0;
    require value <= balance_sender && value <= curr_allowance;

	bool res = transferFrom(e, e.msg.sender, e.msg.sender, value);

	assert res, "Failed self transferFrom";
	assert balance_sender == balanceOf(e.msg.sender), "Self transferFrom breaks accounting";
}


/**
 * @id ERC20_BASE_009
 * @dev Transfers for more than available balance should not be allowed
 * @language CVL
 */
rule ERC20_BASE_009(address to, uint256 value){
	env e;
	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 balance_receiver = balanceOf(to);

    require e.msg.sender != 0;
    require balance_sender < value;

	transfer@withrevert(e, to, value);

    assert lastReverted, "Transfer for more than balance did not revert";
	assert balance_sender == balanceOf(e.msg.sender), "Transfer for more than balance modified source balance";
	assert balance_receiver == balanceOf(to), "Transfer for more than balance modified target balance";
}

/**
 * @id ERC20_BASE_010
 * @dev Transfers for more than available balance should not be allowed
 * @language CVL
 */
rule ERC20_BASE_010(address to, uint256 value) {
	env e;
	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 balance_receiver = balanceOf(to);
	uint256 curr_allowance = allowance(e,e.msg.sender, currentContract);

    require e.msg.sender != 0;
	require curr_allowance > balance_sender;
    require balance_sender < value;

	bool res = transferFrom@withrevert(e,e.msg.sender, to, value);

    assert lastReverted, "TransferFrom for more than balance should revert";
	assert balance_sender == balanceOf(e.msg.sender), "TransferFrom for more than balance modified source balance";
	assert balance_receiver == balanceOf(to), "TransferFrom for more than balance modified target balance";
}


/**
 * @id ERC20_BASE_011
 * @dev Zero amount transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_011(address to){
	env e;
	uint256 balance_sender = balanceOf(currentContract);
	uint256 balance_receiver = balanceOf(to);

    require e.msg.sender != 0;
	require balance_sender > 0;

	bool res = transfer(e, to, 0);

	assert res, "Zero amount transfer failed";
	assert balance_sender == balanceOf(currentContract), "Zero amount transfer modified source balance";
	assert balance_receiver == balanceOf(to), "Zero amount transfer modified target balance";
}

/**
 * @id ERC20_BASE_012
 * @dev Zero amount transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_012(address to){
	env e;
	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 balance_receiver = balanceOf(to);
	uint256 curr_allowance = allowance(e,e.msg.sender, currentContract);

    require e.msg.sender != 0;
	require balance_sender > 0 && curr_allowance > 0;

	bool res = transferFrom(e, e.msg.sender, to, 0);

	assert res, "Zero amount transferFrom failed";
	assert balance_sender == balanceOf(e.msg.sender), "Zero amount transfer modified source balance";
	assert balance_receiver == balanceOf(to), "Zero amount transfer modified target balance";
}


/**
 * @id ERC20_BASE_013
 * @dev Transfers should update accounting correctly
 * @language CVL
 */
rule ERC20_BASE_013(address to, uint256 value){
	env e;
	require to != e.msg.sender;

	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 balance_receiver = balanceOf(to);

	require balance_sender > 2;
    require value <= balance_sender && value > 0;

	bool res = transfer(e, to, value);

	assert res, "Transfer failed";
	assert assert_uint256(balance_sender - value) == balanceOf(e.msg.sender), "Wrong source balance after transfer";
	assert assert_uint256(balance_receiver + value) == balanceOf(to), "Wrong target balance after transfer";
}


/**
 * @id ERC20_BASE_014
 * @dev Transfers should update accounting correctly
 * @language CVL
 */
rule ERC20_BASE_014(address to, uint256 value){
	env e;
	require to != currentContract;
	require to != e.msg.sender;

	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 balance_receiver = balanceOf(to);
	uint256 curr_allowance = allowance(e,e.msg.sender, currentContract);

	require balance_sender > 2 && curr_allowance > balance_sender;
    require value <= balance_sender && value > 0;

	bool res = transferFrom(e, e.msg.sender, to, value);

	assert res, "TransferFrom failed";
	assert assert_uint256(balance_sender - value) == balanceOf(e.msg.sender), "Wrong source balance after transfer";
	assert assert_uint256(balance_receiver + value) == balanceOf(to), "Wrong target balance after transfer";
}


// Rule: Approve should set correct allowances
// invariant ERC20_BASE_015_inv(address sender, address to, uint256 value)
//     approve(to,value) &&
//     allowance(sender, to) == value{
//         preserved {
//             requireInvariant ERC20_BASE_015_inv(e.msg.sender, to, value);
//         }
//     }

/**
 * @id ERC20_BASE_015
 * @dev Approve should set correct allowances
 * @language CVL
 */
rule ERC20_BASE_015(address to , uint256 value){
	env e;
	bool res = approve(e, to, value);

	assert res, "Failed to set allowance via approve";
	assert allowance(e, e.msg.sender, to) == value, "Allowance not set correctly";
}


/**
 * @id ERC20_BASE_016
 * @dev Approve should set correct allowances
 * @language CVL
 */
rule ERC20_BASE_016(address to , uint256 value, uint256 value2){
    env e;
    bool res = approve(e, to, value);

	assert res, "Failed to set allowance via approve";
	assert allowance(e, e.msg.sender, to) == value, "Allowance not set correctly";

    require value2 < value;

	bool res2 = approve(e, to, value2);

	assert res2, "Failed to set allowance via approve";
	assert allowance(e, e.msg.sender, to) == value2, "Allowance not set correctly";
}




/**
 * @id ERC20_BASE_017
 * @dev TransferFrom should decrease allowance
 * @language CVL
 */
rule ERC20_BASE_017(address to , uint256 value){
	env e;

	require to != currentContract && to != 0;
	require to != e.msg.sender;

	uint256 balance_sender = balanceOf(e.msg.sender);
	uint256 curr_allowance = allowance(e,e.msg.sender, currentContract);

	require balance_sender > 0 && curr_allowance > balance_sender;
    require value > 0 && value <= balance_sender;

	bool res = transferFrom(e, e.msg.sender, to, value);

	assert res, "TransferFrom failed";
    // if (curr_allowance != max_uint256) {
        assert assert_uint256(curr_allowance - value) == allowance(e, e.msg.sender, currentContract), "Allowance not updated correctly";
    // }
}



/*
    The function below just calls (dispatch) all methods (an arbitrary one) from the contract,
    using given [env e], [address from] and [address to].
    We use this function in several rules. The usecase is typically to show that
    the call of the function does not affect a "property" of a third party (i.e. != e.msg.sender, from, to),
    such as the balance or allowance.

*/
// function callFunctionWithParams(env e, method f, address from, address to) {
//     uint256 amount;

//     if (f.selector == sig:transfer(address, uint256).selector) {
//         transfer(e, to, amount);
//     } else if (f.selector == sig:allowance(address, address).selector) {
//         allowance(e, from, to);
//     } else if (f.selector == sig:approve(address, uint256).selector) {
//         approve(e, to, amount);
//     } else if (f.selector == sig:transferFrom(address, address, uint256).selector) {
//         transferFrom(e, from, to, amount);
//     } else if (f.selector == sig:increaseAllowance(address, uint256).selector) {
//         increaseAllowance(e, to, amount);
//     } else if (f.selector == sig:decreaseAllowance(address, uint256).selector) {
//         decreaseAllowance(e, to, amount);
//     } else if (f.selector == sig:mint(address, uint256).selector) {
//         mint(e, to, amount);
//     } else if (f.selector == sig:burn(address, uint256).selector) {
//         burn(e, from, amount);
//     } else {
//         calldataarg args;
//         f(e, args);
//     }
// }


/**
 * @id transferReverts
 * @dev Transfer must revert if the sender's balance is too small
 * @language CVL
 */
rule transferReverts(address recipient, uint amount) {
    env e;

    require balanceOf(e.msg.sender) < amount;

    transfer@withrevert(e, recipient, amount);

    assert lastReverted,
        "transfer(recipient,amount) must revert if sender's balance is less than `amount`";
}


/**
 * @id transferDoesntRevert
 * @dev Transfer must not revert unless - the sender doesn't have enough funds, - or the message value is nonzero, - or the recipient's balance would overflow, - or the message sender is 0, - or the recipient is 0
 * @language CVL
 */
rule transferDoesntRevert(address recipient, uint amount) {
    env e;

    require balanceOf(e.msg.sender) > amount;
    require e.msg.value == 0;  // No payment

    // This requirement prevents overflow of recipient's balance.
    // We convert `max_uint` to type `mathint` since:
    //   1. a sum always returns type `mathint`, hence the left hand side is `mathint`,
    //   2. `mathint` can only be compared to another `mathint`
    require balanceOf(recipient) + amount < to_mathint(max_uint);

    // Recall that `address(0)` is a special address that in general should not be used
    require e.msg.sender != 0;
    require recipient != 0;

    transfer@withrevert(e, recipient, amount);
    assert !lastReverted;
}

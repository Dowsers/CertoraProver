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
    function transfer(address,uint256) external returns bool;
    function transferFrom(address,address,uint256) external returns bool;
    function approve(address,uint256) external returns bool;
}



// Rule: Total supply should change only by means of mint or burn
rule ERC20_BASE_001(method f) {

	mathint totalSupplyBefore = totalSupply();

	env e;
	calldataarg args;
	f(e,args);

	assert totalSupply() == totalSupplyBefore, "Total supply changed without mint or burn";

	assert (
		totalSupply() == totalSupplyBefore  =>
			( f.selector == sig:mint(address,uint256) ||
			f.selector == sig:burn(address,uint256) ||
			f.selector == sig:burnFrom(address,address,uint256) ),
		"Total supply changed without mint, burn or burnFrom");
}



// Rule: Each user's balance must not exceed the total supply
invariant ERC20_BASE_002(address user)
    balanceOf(user) <= totalSupply();

// rule ERC20_BASE_002(address user) {
//     assert balanceOf(user) <= totalSupply(), "User balance higher than total supply";
// }



// Rule: Sum of specified user balances must not exceed total supply
ghost mathint totalUserBalances;

hook Sstore balanceOf[KEY address user]
    bool newVal (bool oldVal) {
    totalUserBalances = totalUserBalances + balancesOf(user);
}
invariant ERC20_BASE_003()
    to_mathint(totalSupply()) >= totalUserBalances;

// rule ERC20_BASE_003() {

//     env e;
//     // Define the addresses of specific users to check
//     address everyUser1;
//     address everyUser2;
//     address everyUser3;

//     mathint totalUserBalances = balanceOf(everyUser1) + balanceOf(everyUser2) + balanceOf(everyUser3);

//     // Ensure that the sum of user balances does not exceed the total supply
//     assert assert_uint256(totalUserBalances) <= totalSupply(), "Sum of user balances higher than total supply";
// }


/*
    The function below just calls (dispatch) all methods (an arbitrary one) from the contract,
    using given [env e], [address from] and [address to].
    We use this function in several rules. The usecase is typically to show that
    the call of the function does not affect a "property" of a third party (i.e. != e.msg.sender, from, to),
    such as the balance or allowance.

*/
function callFunctionWithParams(env e, method f, address from, address to) {
    uint256 amount;

    if (f.selector == sig:transfer(address, uint256).selector) {
        transfer(e, to, amount);
    } else if (f.selector == sig:allowance(address, address).selector) {
        allowance(e, from, to);
    } else if (f.selector == sig:approve(address, uint256).selector) {
        approve(e, to, amount);
    } else if (f.selector == sig:transferFrom(address, address, uint256).selector) {
        transferFrom(e, from, to, amount);
    } else if (f.selector == sig:increaseAllowance(address, uint256).selector) {
        increaseAllowance(e, to, amount);
    } else if (f.selector == sig:decreaseAllowance(address, uint256).selector) {
        decreaseAllowance(e, to, amount);
    } else if (f.selector == sig:mint(address, uint256).selector) {
        mint(e, to, amount);
    } else if (f.selector == sig:burn(address, uint256).selector) {
        burn(e, from, amount);
    } else {
        calldataarg args;
        f(e, args);
    }
}



/** @title Transfer must move `amount` tokens from the caller's
 *  account to `recipient`
 */
rule transferSpec(address recipient, uint amount) {

    env e;

    // `mathint` is a type that represents an integer of any size
    mathint balance_sender_before = balanceOf(e.msg.sender);
    mathint balance_recip_before = balanceOf(recipient);

    transfer(e, recipient, amount);

    mathint balance_sender_after = balanceOf(e.msg.sender);
    mathint balance_recip_after = balanceOf(recipient);

    // Operations on mathints can never overflow nor underflow
    assert balance_sender_after == balance_sender_before - amount,
        "transfer must decrease sender's balance by amount";

    assert balance_recip_after == balance_recip_before + amount,
        "transfer must increase recipient's balance by amount";
}


/// @title Transfer must revert if the sender's balance is too small
rule transferReverts(address recipient, uint amount) {
    env e;

    require balanceOf(e.msg.sender) < amount;

    transfer@withrevert(e, recipient, amount);

    assert lastReverted,
        "transfer(recipient,amount) must revert if sender's balance is less than `amount`";
}


/** @title Transfer must not revert unless
 * - the sender doesn't have enough funds,
 * - or the message value is nonzero,
 * - or the recipient's balance would overflow,
 * - or the message sender is 0,
 * - or the recipient is 0
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

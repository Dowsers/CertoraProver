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
rule ERC20_BASE_001(env e, method f) {
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
rule ERC20_BASE_002(env e, method f) {

    require e.msg.sender != 0;
    calldataarg args;

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


// Rule: Address zero should have zero balance
invariant ERC20_BASE_004()
    to_mathint(balanceOf(0)) == 0;


/**
 * @id ERC20_BASE_005
 * @dev Transfers to the zero address should not be allowed
 * @language CVL
 */
rule ERC20_BASE_005(env e) {
    address holder;
    address recipient = 0;
	uint256 amount = balanceOf(holder);
	bool res = transfer@withrevert(e, recipient, amount);
    assert lastReverted || !res, "Transfer to address zero did not revert or succeeded unexpectedly";
}


/**
 * @id ERC20_BASE_006
 * @dev Transfers to zero address should not be allowed
 * @language CVL
 */
rule ERC20_BASE_006(env e) {

    address spender = e.msg.sender;
    address holder;
    address recipient = 0;
    uint256 amount;

	uint256 balance_sender = balanceOf(holder);
	uint256 curr_allowance = allowance(e, holder, spender);

    require amount <= curr_allowance  && amount <= balance_sender;

	bool res = transferFrom@withrevert(e, holder, recipient, amount);
    assert lastReverted || !res, "Transfer to address zero did not revert or succeeded unexpectedly";
}


/**
 * @id ERC20_BASE_007
 * @dev Self transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_007(env e){
    requireInvariant ERC20_BASE_003();

    address holder = e.msg.sender;
    uint256 amount;

    require holder != 0;

    // cache state
    uint256 holderBalanceBefore    = balanceOf(holder);

    require amount <= holderBalanceBefore;
    require holderBalanceBefore > 0;

    // run transaction
    bool res = transfer(e, holder, amount);

    // check outcome
    assert res, "Failed self transfer";
    // balance of holder remains unchanged
    assert balanceOf(holder) == holderBalanceBefore, "Self transfer breaks accounting";
}






/**
 * @id ERC20_BASE_008
 * @dev Self transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_008(env e){
    requireInvariant ERC20_BASE_003();

    address spender = e.msg.sender;
    address holder;
    uint256 amount;

    require holder != 0;

    // cache state
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 allowanceBefore        = allowance(holder, spender);

    require amount <= holderBalanceBefore;
    require holderBalanceBefore > 0 && allowanceBefore > 0;
    require amount <= holderBalanceBefore && amount <= allowanceBefore;

    // run transaction
    bool res = transferFrom(e, holder, holder, amount);

    // check outcome
	assert res, "Failed self transferFrom";
    // balance of holder remains unchanged
    assert balanceOf(holder) == holderBalanceBefore, "Self transferFrom breaks accounting";
}



/**
 * @id ERC20_BASE_009
 * @dev Transfers for more than available balance should not be allowed
 * @language CVL
 */
rule ERC20_BASE_009(env e){
    requireInvariant ERC20_BASE_003();

    address holder;
    address recipient;
    uint256 amount;

	uint256 holderBalanceBefore = balanceOf(holder);
	uint256 recipientBalanceBefore = balanceOf(recipient);

    require holder!= 0;
    require holderBalanceBefore < amount;

	transfer@withrevert(e, recipient, amount);

    assert lastReverted, "Transfer for more than balance did not revert";
	assert holderBalanceBefore == balanceOf(holder), "Transfer for more than balance modified source balance";
	assert recipientBalanceBefore == balanceOf(recipient), "Transfer for more than balance modified target balance";
}

/**
 * @id ERC20_BASE_010
 * @dev Transfers for more than available balance should not be allowed
 * @language CVL
 */
rule ERC20_BASE_010(env e) {
    requireInvariant ERC20_BASE_003();

    address spender = e.msg.sender;
    address holder;
    address recipient;
    uint256 amount;

    require holder != 0 && recipient != 0;

	uint256 holderBalanceBefore = balanceOf(holder);
	uint256 recipientBalanceBefore = balanceOf(to);
	uint256 allowanceBefore = allowance(e, holder, spender);

	require allowanceBefore > holderBalanceBefore;
    require holderBalanceBefore < value;

	bool res = transferFrom@withrevert(e, holder, recipient, value);

    assert lastReverted, "TransferFrom for more than balance should revert";
	assert holderBalanceBefore == balanceOf(holder), "TransferFrom for more than balance modified source balance";
	assert recipientBalanceBefore == balanceOf(to), "TransferFrom for more than balance modified target balance";
}


/**
 * @id ERC20_BASE_011
 * @dev Zero amount transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_011(env e){
    requireInvariant ERC20_BASE_003();
    address holder = e.msg.sender;
    address recipient;
    uint256 amount = 0;

    require holder != 0;

    // cache state
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);

    require holderBalanceBefore > 0;

    // run transaction
    bool res = transfer(e, recipient, amount);

    // check outcome
    assert res, "Zero amount transfer failed";

    // balances of holder and recipient are updated
    assert balanceOf(holder) == holderBalanceBefore, "Zero amount transfer modified source balance";
    assert balanceOf(recipient) == recipientBalanceBefore, "Zero amount transfer modified target balance";
}



/**
 * @id ERC20_BASE_012
 * @dev Zero amount transfers should not break accounting
 * @language CVL
 */
rule ERC20_BASE_012(env e){
    requireInvariant ERC20_BASE_003();
    address spender = e.msg.sender;
    address holder;
    address recipient;
    uint256 amount = 0;

    require recipient != 0 && holder != 0;

    // cache state
    uint256 allowanceBefore        = allowance(holder, spender);
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);

    require holderBalanceBefore > 0 && allowanceBefore > 0;

    // run transaction
    bool res = transferFrom(e, holder, recipient, amount);

    // check outcome
    assert res, "Zero amount transferFrom failed";
    // balances of holder and recipient are updated
    assert balanceOf(holder)    == holderBalanceBefore, "Zero amount transfer modified source balance";
    assert balanceOf(recipient) == recipientBalanceBefore, , "Zero amount transfer modified target balance";
}



/**
 * @id ERC20_BASE_013
 * @dev Transfers should update accounting correctly
 * @language CVL
 */
rule ERC20_BASE_013(env e) {
    requireInvariant ERC20_BASE_003();

    address holder = e.msg.sender;
    address recipient;
    uint256 amount;

    // cache state
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);

    // run transaction
    bool res = transfer(e, recipient, amount);

    // check outcome
    assert res, "Transfer failed";
    // balances of holder and recipient are updated
    assert balanceOf(holder) == holderBalanceBefore    - (holder == recipient ? 0 : amount);
    assert balanceOf(recipient) == recipientBalanceBefore + (holder == recipient ? 0 : amount);
}


/**
 * @id ERC20_BASE_014
 * @dev Transfers should update accounting correctly
 * @language CVL
 */
rule ERC20_BASE_014(env e){
    requireInvariant ERC20_BASE_003();

    address spender = e.msg.sender;
    address holder;
    address recipient;
    uint256 amount;

    require recipient != 0 && holder != 0;
    require recipient != holder;

    // cache state
    uint256 allowanceBefore        = allowance(holder, spender);
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);

    require(holderBalanceBefore > 0 && allowanceBefore > holderBalanceBefore);

    // run transaction
    bool res = transferFrom(e, holder, recipient, amount);

    // check outcome
    assert res, "TransferFrom failed";

    // balances of holder and recipient are updated
    assert balanceOf(holder)    == holderBalanceBefore    - (holder == recipient ? 0 : amount);
    assert balanceOf(recipient) == recipientBalanceBefore + (holder == recipient ? 0 : amount);
}


/**
 * @id ERC20_BASE_015
 * @dev Approve should set correct allowances
 * @language CVL
 */
rule ERC20_BASE_015(env e) {
    address holder = e.msg.sender;
    address spender;
    uint256 amount;

    approve(e, spender, amount);

    assert allowance(holder, spender) == amount, "Allowance not set correctly";
}




/**
 * @id ERC20_BASE_016
 * @dev Approve should set correct allowances
 * @language CVL
 */
rule ERC20_BASE_016(env e){
    address holder = e.msg.sender;
    address spender;
    uint256 amount;
    uint256 amount2;

    bool res = approve(e, spender, amount);

    assert res, "Failed to set allowance via approve";
    // check allowance
    assert allowance(holder, spender) == amount, "Allowance not set correctly";

    require amount2 < amount;

	res2 = approve(e, spender, amount2);

	assert res2, "Failed to set allowance via approve (seond time)";
    // check allowance
	assert allowance(e, holder, spender) == value2, "Allowance not set correctly";
}




/**
 * @id ERC20_BASE_017
 * @dev TransferFrom should decrease allowance
 * @language CVL
 */
rule ERC20_BASE_017(env e){
    requireInvariant ERC20_BASE_003();

    address spender = e.msg.sender;
    address holder;
    address recipient;
    uint256 amount;

    // cache state
    uint256 allowanceBefore        = allowance(holder, spender);
    uint256 holderBalanceBefore    = balanceOf(holder);
    uint256 recipientBalanceBefore = balanceOf(recipient);

    require(holderBalanceBefore > 0 && allowanceBefore > holderBalanceBefore);

    // run transaction
    transferFrom(e, holder, recipient, amount);

    uint256 allowanceAfter = assert_uint256(allowance(holder, spender));
    if (allowanceBefore != max_uint256) {
        uint256 expectedAllowance = assert_uint256(allowanceBefore == max_uint256 ? max_uint256 : allowanceBefore - amount);

        // allowance is valid & updated
        assert allowanceBefore >= amount;
        assert (allowanceAfter == expectedAllowance);

        // balances of holder and recipient are updated
        assert balanceOf(holder)    == holderBalanceBefore    - (holder == recipient ? 0 : amount);
        assert balanceOf(recipient) == recipientBalanceBefore + (holder == recipient ? 0 : amount);
    }
    else assert true;
}



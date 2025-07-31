/*
### ID
HumanEval/76
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power::pow;
use vstd::prelude::*;
verus! {

// note that the order of paramters is reverse in exec fn ilog and spec fn log
#[verifier::external_fn_specification]
pub fn ex_ilog(x: u32, base: u32) -> (ret: u32)
    requires
        x > 0,
        base > 1,
    ensures
        ret == log(base as int, x as int),
{
    x.ilog(base)
}

#[verifier::external_fn_specification]
pub fn ex_checked_pow(x: u32, exp: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() <==> ret.unwrap() == pow(x as int, exp as nat),
        ret.is_none() <==> pow(x as int, exp as nat) > u32::MAX,
{
    x.checked_pow(exp)
}

fn is_simple_power(x: u32, n: u32) -> (ret: bool)
    requires
        x > 0,
        n > 1,
    ensures
        ret <==> x == pow(n as int, log(n as int, x as int) as nat),
{
    let maybe_x = n.checked_pow(x.ilog(n));
    return maybe_x.is_some() && maybe_x.unwrap() == x;
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def is_simple_power(x, n):
    """Your task is to write a function that returns true if a number x is a simple
    power of n and false in other cases.
    x is a simple power of n if n**int=x
    For example:
    is_simple_power(1, 4) => true
    is_simple_power(2, 2) => true
    is_simple_power(8, 2) => true
    is_simple_power(3, 2) => false
    is_simple_power(3, 1) => false
    is_simple_power(5, 3) => false
    """

*/

/*
### ENTRY POINT
is_simple_power
*/

/*
### CANONICAL SOLUTION
    if (n == 1):
        return (x == 1)
    power = 1
    while (power < x):
        power = power * n
    return (power == x)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(16, 2)== True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(143214, 16)== False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(4, 2)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(9, 3)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(16, 4)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(24, 2)==False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(128, 4)==False, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(12, 6)==False, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1, 1)==True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(1, 12)==True, "This prints if this assert fails 2 (also good for debugging!)"


*/

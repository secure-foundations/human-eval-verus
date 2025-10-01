/*
### ID
HumanEval/97
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::div_mod::*;
use vstd::math::abs as vabs;
use vstd::prelude::*;

use vstd::arithmetic::mul::lemma_mul_upper_bound;

verus! {

pub proof fn lemma_mul_ub_mod_abs(x: int, y: int, a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        0 <= (vabs(x) % (a as nat)) * (vabs(y) % (b as nat)) <= (a * b),
{
    lemma_mul_upper_bound((vabs(x) % (a as nat)) as int, a, (vabs(y) % (b as nat)) as int, b);
}

fn unit_digit(a: i32) -> (ret: i32)
    ensures
        ret as int == vabs(a as int) % 10,
{
    let result = if a < 0 {
        -(a % 10)
    } else {
        a % 10
    };
    result
}

pub open spec fn multiply_spec(a: int, b: int) -> nat {
    (vabs(a) % 10) * (vabs(b) % 10)
}

fn multiply(a: i32, b: i32) -> (ret: i32)
    ensures
        ret as int == multiply_spec(a as int, b as int),
{
    assert(0 <= (vabs(a as int) % 10) * (vabs(b as int) % 10) <= 100) by {
        lemma_mul_ub_mod_abs(a as int, b as int, 10, 10)
    };

    unit_digit(a) * unit_digit(b)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def multiply(a, b):
    """Complete the function that takes two integers and returns
    the product of their unit digits.
    Assume the input is always valid.
    Examples:
    multiply(148, 412) should return 16.
    multiply(19, 28) should return 72.
    multiply(2020, 1851) should return 0.
    multiply(14,-15) should return 20.
    """

*/

/*
### ENTRY POINT
multiply
*/

/*
### CANONICAL SOLUTION
    return abs(a % 10) * abs(b % 10)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(148, 412) == 16, "First test error: " + str(candidate(148, 412))
    assert candidate(19, 28) == 72, "Second test error: " + str(candidate(19, 28))
    assert candidate(2020, 1851) == 0, "Third test error: " + str(candidate(2020, 1851))
    assert candidate(14,-15) == 20, "Fourth test error: " + str(candidate(14,-15))
    assert candidate(76, 67) == 42, "Fifth test error: " + str(candidate(76, 67))
    assert candidate(17, 27) == 49, "Sixth test error: " + str(candidate(17, 27))


    # Check some edge cases that are easy to work out by hand.
    assert candidate(0, 1) == 0, "1st edge test error: " + str(candidate(0, 1))
    assert candidate(0, 0) == 0, "2nd edge test error: " + str(candidate(0, 0))


*/

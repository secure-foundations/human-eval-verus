/*
### ID
HumanEval/138
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn is_equal_to_sum_even(n: u32) -> (b: bool)  // 2 + 2 + 2 + (n - 6)
    ensures
        b <==> n % 2 == 0 && n >= 8,
{
    n % 2 == 0 && n >= 8
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def is_equal_to_sum_even(n):
    """Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
    Example
    is_equal_to_sum_even(4) == False
    is_equal_to_sum_even(6) == False
    is_equal_to_sum_even(8) == True
    """

*/

/*
### ENTRY POINT
is_equal_to_sum_even
*/

/*
### CANONICAL SOLUTION
    return n%2 == 0 and n >= 8

*/

/*
### TEST
def check(candidate):
    assert candidate(4) == False
    assert candidate(6) == False
    assert candidate(8) == True
    assert candidate(10) == True
    assert candidate(11) == False
    assert candidate(12) == True
    assert candidate(13) == False
    assert candidate(16) == True

*/

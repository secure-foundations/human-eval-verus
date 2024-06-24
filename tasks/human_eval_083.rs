
/*
### ID
HumanEval/83
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

    // TODO: Put your solution (the specification, implementation, and proof) to the task here
 

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def starts_one_ends(n):
    """
    Given a positive integer n, return the count of the numbers of n-digit
    positive integers that start or end with 1.
    """

*/

/*
### ENTRY POINT
starts_one_ends
*/

/*
### CANONICAL SOLUTION
    if n == 1: return 1
    return 18 * (10 ** (n - 2))

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(1) == 1
    assert candidate(2) == 18
    assert candidate(3) == 180
    assert candidate(4) == 1800
    assert candidate(5) == 18000

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"


*/


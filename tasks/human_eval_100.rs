/*
### ID
HumanEval/100
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn make_a_pile(n: usize) -> (pile: Vec<usize>)
    requires
        n + (2 * n) <= usize::MAX,
    ensures
        pile.len() == n,
        n > 0 ==> pile[0] == n,
        forall|i: int| #![trigger pile[i]] 1 <= i < n ==> pile[i] == pile[i - 1] + 2,
{
    if n == 0 {
        return vec![];
    }
    let mut pile = vec![n];
    for i in 1..n
        invariant
            pile.len() == i,
            pile[i - 1] + (2 * (n - i)) <= usize::MAX,
            forall|j: int| #![trigger pile[j]] 1 <= j < i ==> pile[j] == pile[j - 1] + 2,
            n > 0 ==> pile[0] == n,
    {
        let prev = pile[i - 1];
        pile.push(prev + 2);
    }
    pile
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def make_a_pile(n):
    """
    Given a positive integer n, you have to make a pile of n levels of stones.
    The first level has n stones.
    The number of stones in the next level is:
        - the next odd number if n is odd.
        - the next even number if n is even.
    Return the number of stones in each level in a list, where element at index
    i represents the number of stones in the level (i+1).

    Examples:
    >>> make_a_pile(3)
    [3, 5, 7]
    """

*/

/*
### ENTRY POINT
make_a_pile
*/

/*
### CANONICAL SOLUTION
    return [n + 2*i for i in range(n)]

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(3) == [3, 5, 7], "Test 3"
    assert candidate(4) == [4,6,8,10], "Test 4"
    assert candidate(5) == [5, 7, 9, 11, 13]
    assert candidate(6) == [6, 8, 10, 12, 14, 16]
    assert candidate(8) == [8, 10, 12, 14, 16, 18, 20, 22]

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"


*/

/*
### ID
HumanEval/90
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

def next_smallest(lst):
    """
    You are given a list of integers.
    Write a function next_smallest() that returns the 2nd smallest element of the list.
    Return None if there is no such element.

    next_smallest([1, 2, 3, 4, 5]) == 2
    next_smallest([5, 1, 4, 3, 2]) == 2
    next_smallest([]) == None
    next_smallest([1, 1]) == None
    """

*/

/*
### ENTRY POINT
next_smallest
*/

/*
### CANONICAL SOLUTION
    lst = sorted(set(lst))
    return None if len(lst) < 2 else lst[1]

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4, 5]) == 2
    assert candidate([5, 1, 4, 3, 2]) == 2
    assert candidate([]) == None
    assert candidate([1, 1]) == None
    assert candidate([1,1,1,1,0]) == 1
    assert candidate([1, 0**0]) == None
    assert candidate([-35, 34, 12, -45]) == -35

    # Check some edge cases that are easy to work out by hand.
    assert True


*/

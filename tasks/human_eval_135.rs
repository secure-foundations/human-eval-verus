/*
### ID
HumanEval/135
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

def can_arrange(arr):
    """Create a function which returns the largest index of an element which
    is not greater than or equal to the element immediately preceding it. If
    no such element exists then return -1. The given array will not contain
    duplicate values.

    Examples:
    can_arrange([1,2,4,3,5]) = 3
    can_arrange([1,2,3]) = -1
    """

*/

/*
### ENTRY POINT
can_arrange
*/

/*
### CANONICAL SOLUTION
    ind=-1
    i=1
    while i<len(arr):
      if arr[i]<arr[i-1]:
        ind=i
      i+=1
    return ind

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,4,3,5])==3
    assert candidate([1,2,4,5])==-1
    assert candidate([1,4,2,5,6,7,8,9,10])==2
    assert candidate([4,8,5,7,3])==4

    # Check some edge cases that are easy to work out by hand.
    assert candidate([])==-1


*/

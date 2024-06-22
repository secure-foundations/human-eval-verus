
/*
### ID
HumanEval/85
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

 

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def add(lst):
    """Given a non-empty list of integers lst. add the even elements that are at odd indices..


    Examples:
        add([4, 2, 6, 7]) ==> 2 
    """

*/

/*
### ENTRY POINT
add
*/

/*
### CANONICAL SOLUTION
    return sum([lst[i] for i in range(1, len(lst), 2) if lst[i]%2 == 0])

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([4, 88]) == 88
    assert candidate([4, 5, 6, 7, 2, 122]) == 122
    assert candidate([4, 0, 6, 7]) == 0
    assert candidate([4, 4, 6, 8]) == 12

    # Check some edge cases that are easy to work out by hand.
    

*/


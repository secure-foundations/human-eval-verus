
/*
### ID
HumanEval/5
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
from typing import List


def intersperse(numbers: List[int], delimeter: int) -> List[int]:
    """ Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
    >>> intersperse([], 4)
    []
    >>> intersperse([1, 2, 3], 4)
    [1, 4, 2, 4, 3]
    """

*/

/*
### ENTRY POINT
intersperse
*/

/*
### CANONICAL SOLUTION
    if not numbers:
        return []

    result = []

    for n in numbers[:-1]:
        result.append(n)
        result.append(delimeter)

    result.append(numbers[-1])

    return result

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 7) == []
    assert candidate([5, 6, 3, 2], 8) == [5, 8, 6, 8, 3, 8, 2]
    assert candidate([2, 2, 2], 2) == [2, 2, 2, 2, 2]

*/


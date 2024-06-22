
/*
### ID
HumanEval/13
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


def greatest_common_divisor(a: int, b: int) -> int:
    """ Return a greatest common divisor of two integers a and b
    >>> greatest_common_divisor(3, 5)
    1
    >>> greatest_common_divisor(25, 15)
    5
    """

*/

/*
### ENTRY POINT
greatest_common_divisor
*/

/*
### CANONICAL SOLUTION
    while b:
        a, b = b, a % b
    return a

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3, 7) == 1
    assert candidate(10, 15) == 5
    assert candidate(49, 14) == 7
    assert candidate(144, 60) == 12

*/


/*
### ID
HumanEval/53
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn add(x: i32, y: i32) -> (res: Option<i32>)
    ensures
        res.is_some() ==> res.unwrap() == x + y,
{
    x.checked_add(y)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def add(x: int, y: int):
    """Add two numbers x and y
    >>> add(2, 3)
    5
    >>> add(5, 7)
    12
    """

*/

/*
### ENTRY POINT
add
*/

/*
### CANONICAL SOLUTION
    return x + y

*/

/*
### TEST


METADATA = {}


def check(candidate):
    import random

    assert candidate(0, 1) == 1
    assert candidate(1, 0) == 1
    assert candidate(2, 3) == 5
    assert candidate(5, 7) == 12
    assert candidate(7, 5) == 12

    for i in range(100):
        x, y = random.randint(0, 1000), random.randint(0, 1000)
        assert candidate(x, y) == x + y


*/

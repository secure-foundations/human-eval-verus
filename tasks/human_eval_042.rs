
/*
### ID
HumanEval/42
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    requires
        forall |i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX, // avoid overflow
    ensures
        result.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
{
    let mut result = Vec::with_capacity(l.len());
    for i in 0..l.len()
        invariant
            forall |i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
            result.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1,
    {
        result.push(l[i] + 1);
    }
    result
}

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def incr_list(l: list):
    """Return list with elements incremented by 1.
    >>> incr_list([1, 2, 3])
    [2, 3, 4]
    >>> incr_list([5, 3, 5, 2, 3, 3, 9, 0, 123])
    [6, 4, 6, 3, 4, 4, 10, 1, 124]
    """

*/

/*
### ENTRY POINT
incr_list
*/

/*
### CANONICAL SOLUTION
    return [(e + 1) for e in l]

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([]) == []
    assert candidate([3, 2, 1]) == [4, 3, 2]
    assert candidate([5, 2, 5, 2, 3, 3, 9, 0, 123]) == [6, 3, 6, 3, 4, 4, 10, 1, 124]


*/


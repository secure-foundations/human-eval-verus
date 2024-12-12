/*
### ID
HumanEval/35
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn max_element(a: &Vec<i32>) -> (max: i32)
    requires
        a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
{
    let mut max = a[0];
    for i in 1..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a[j] <= max,
            exists|j: int| 0 <= j < i && a[j] == max,
    {
        if a[i] > max {
            max = a[i];
        }
    }
    max
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def max_element(l: list):
    """Return maximum element in the list.
    >>> max_element([1, 2, 3])
    3
    >>> max_element([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
    123
    """

*/

/*
### ENTRY POINT
max_element
*/

/*
### CANONICAL SOLUTION
    m = l[0]
    for e in l:
        if e > m:
            m = e
    return m

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([1, 2, 3]) == 3
    assert candidate([5, 3, -5, 2, -3, 3, 9, 0, 124, 1, -10]) == 124

*/

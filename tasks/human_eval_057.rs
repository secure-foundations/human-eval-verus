/*
### ID
HumanEval/57
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn monotonic(l: Vec<i32>) -> (ret: bool)
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
{
    if l.len() == 0 || l.len() == 1 {
        return true;
    }
    let mut increasing = true;
    let mut decreasing = true;

    let mut n = 0;
    while n < l.len() - 1
        invariant
            l.len() > 1,
            n <= l.len() - 1,
            increasing <==> forall|i: int, j: int|
                0 <= i < j < n + 1 ==> l@.index(i) <= l@.index(j),
            decreasing <==> forall|i: int, j: int|
                0 <= i < j < n + 1 ==> l@.index(i) >= l@.index(j),
        decreases l.len() - 1 - n,
    {
        if l[n] < l[n + 1] {
            decreasing = false;
        } else if l[n] > l[n + 1] {
            increasing = false;
        }
        n += 1;
    }
    increasing || decreasing
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def monotonic(l: list):
    """Return True is list elements are monotonically increasing or decreasing.
    >>> monotonic([1, 2, 4, 20])
    True
    >>> monotonic([1, 20, 4, 10])
    False
    >>> monotonic([4, 1, 0, -10])
    True
    """

*/

/*
### ENTRY POINT
monotonic
*/

/*
### CANONICAL SOLUTION
    if l == sorted(l) or l == sorted(l, reverse=True):
        return True
    return False

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([1, 2, 4, 10]) == True
    assert candidate([1, 2, 4, 20]) == True
    assert candidate([1, 20, 4, 10]) == False
    assert candidate([4, 1, 0, -10]) == True
    assert candidate([4, 1, 1, 0]) == True
    assert candidate([1, 2, 3, 2, 5, 60]) == False
    assert candidate([1, 2, 3, 4, 5, 60]) == True
    assert candidate([9, 9, 9, 9]) == True


*/

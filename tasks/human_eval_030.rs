/*
### ID
HumanEval/30
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
{
    let mut positive_list = Vec::<i32>::new();
    let input_len = input.len();
    assert(input@[..0int].filter(|x: i32| x > 0) == Seq::<i32>::empty());
    for pos in 0..input_len
        invariant
            input_len == input.len(),
            positive_list@ == input@[..pos].filter(|x: i32| x > 0),
    {
        let n = input[pos];
        if n > 0 {
            positive_list.push(n);
        }
        assert(input@[..pos + 1].drop_last() == input@[..pos]);
        reveal(Seq::filter);
    }
    assert(input@ == input@[..input_len]);
    positive_list
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def get_positive(l: list):
    """Return only positive numbers in the list.
    >>> get_positive([-1, 2, -4, 5, 6])
    [2, 5, 6]
    >>> get_positive([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
    [5, 3, 2, 3, 9, 123, 1]
    """

*/

/*
### ENTRY POINT
get_positive
*/

/*
### CANONICAL SOLUTION
    return [e for e in l if e > 0]

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([-1, -2, 4, 5, 6]) == [4, 5, 6]
    assert candidate([5, 3, -5, 2, 3, 3, 9, 0, 123, 1, -10]) == [5, 3, 2, 3, 3, 9, 123, 1]
    assert candidate([-1, -2]) == []
    assert candidate([]) == []


*/

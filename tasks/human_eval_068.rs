/*
### ID
HumanEval/68
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)
    requires
        nodes@.len() <= u32::MAX,
    ensures
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 0 ==> forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        result@.len() == 2 ==> {
            let node = result@[0];
            let index = result@[1];
            &&& 0 <= index < nodes@.len()
            &&& nodes@[index as int] == node
            &&& node % 2 == 0
            &&& forall|i: int|
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|i: int|
                    0 <= i < result@[1] ==> nodes@[i] % 2 != 0 || nodes@[i] > node
        },
{
    let mut smallest_even: Option<u32> = None;
    let mut smallest_index: Option<u32> = None;

    for i in 0..nodes.len()
        invariant
            0 <= i <= nodes@.len(),
            nodes@.len() <= u32::MAX,
            smallest_even.is_none() == smallest_index.is_none(),
            smallest_index.is_none() ==> forall|j: int| 0 <= j < i ==> nodes@[j] % 2 != 0,
            smallest_index.is_some() ==> {
                &&& 0 <= smallest_index.unwrap() < i as int
                &&& nodes@[smallest_index.unwrap() as int] == smallest_even.unwrap()
                &&& smallest_even.unwrap() % 2 == 0
                &&& forall|j: int|
                    0 <= j < i ==> nodes@[j] % 2 == 0 ==> smallest_even.unwrap() <= nodes@[j]
                &&& forall|j: int|
                    0 <= j < smallest_index.unwrap() ==> nodes@[j] % 2 != 0 || nodes@[j]
                        > smallest_even.unwrap()
            },
    {
        if nodes[i] % 2 == 0 && (smallest_even.is_none() || nodes[i] < smallest_even.unwrap()) {
            smallest_even = Some(nodes[i]);
            smallest_index = Some((i as u32));
        }
    }
    if smallest_index.is_none() {
        Vec::new()
    } else {
        vec![smallest_even.unwrap(), smallest_index.unwrap()]
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def pluck(arr):
    """
    "Given an array representing a branch of a tree that has non-negative integer nodes
    your task is to pluck one of the nodes and return it.
    The plucked node should be the node with the smallest even value.
    If multiple nodes with the same smallest even value are found return the node that has smallest index.

    The plucked node should be returned in a list, [ smalest_value, its index ],
    If there are no even values or the given array is empty, return [].

    Example 1:
        Input: [4,2,3]
        Output: [2, 1]
        Explanation: 2 has the smallest even value, and 2 has the smallest index.

    Example 2:
        Input: [1,2,3]
        Output: [2, 1]
        Explanation: 2 has the smallest even value, and 2 has the smallest index.

    Example 3:
        Input: []
        Output: []

    Example 4:
        Input: [5, 0, 3, 0, 4, 2]
        Output: [0, 1]
        Explanation: 0 is the smallest value, but  there are two zeros,
                     so we will choose the first zero, which has the smallest index.

    Constraints:
        * 1 <= nodes.length <= 10000
        * 0 <= node.value
    """

*/

/*
### ENTRY POINT
pluck
*/

/*
### CANONICAL SOLUTION
    if(len(arr) == 0): return []
    evens = list(filter(lambda x: x%2 == 0, arr))
    if(evens == []): return []
    return [min(evens), arr.index(min(evens))]

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([4,2,3]) == [2, 1], "Error"
    assert candidate([1,2,3]) == [2, 1], "Error"
    assert candidate([]) == [], "Error"
    assert candidate([5, 0, 3, 0, 4, 2]) == [0, 1], "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([1, 2, 3, 0, 5, 3]) == [0, 3], "Error"
    assert candidate([5, 4, 8, 4 ,8]) == [4, 1], "Error"
    assert candidate([7, 6, 7, 1]) == [6, 1], "Error"
    assert candidate([7, 9, 7, 1]) == [], "Error"


*/

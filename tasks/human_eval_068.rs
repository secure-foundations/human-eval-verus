/*
### ID
HumanEval/68
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_pluck(s: Seq<usize>) -> Seq<usize>{
    let filtered = s.map(|i: int, x: usize| (i, x)).filter(|p: (int, usize)| p.1 % 2 == 0);
    if filtered.len() == 0 {
        Seq::empty()
    } else {
        let (i, x) = filtered.min_via(|p1: (int, usize), p2: (int, usize)| p1.1 <= p2.1);
        seq![x, i as usize]
    }
}

fn pluck(nodes: &Vec<usize>) -> (ret: Vec<usize>)
    ensures
        ret@ =~= spec_pluck(nodes@),
{
    let mut ret = Vec::new();
    let ghost filtered: Seq<(int, usize)> = Seq::empty();
    let ghost mapped: Seq<(int, usize)> = Seq::empty();
    for i in 0..nodes.len()
        invariant
            ret@ =~= spec_pluck(nodes@.subrange(0, i as int)),
            mapped =~= nodes@.subrange(0, i as int).map(|i: int, x: usize| (i, x)),
            filtered =~= mapped.filter(|p: (int, usize)| p.1 % 2 == 0),
            filtered.len() <= mapped.len() == i as int,
            i <= nodes.len(),
    {
        reveal_with_fuel(Seq::filter, 5);
        reveal_with_fuel(Seq::min_via, 5);
        proof { mapped = mapped.push((i as int, nodes[i as int])); } 
        // assert(mapped.len() == i + 1 as int);
        // assert(mapped.subrange(0, i+1 as int).drop_last() =~= mapped.subrange(0, i as int));
        // assert(nodes@.subrange(0, i+1 as int).drop_last() =~= nodes@.subrange(0, i as int));
        assert(mapped.index(i as int).1 == nodes[i as int]);
        if (nodes[i] % 2 == 0) {
            proof { filtered = filtered.push((i as int, nodes[i as int])); }
            if (ret.len() == 0 || nodes[i] < ret[0]) {
                ret = vec![nodes[i], i];
            }
        }
    }
    assert(nodes@.subrange(0, nodes.len() as int) =~= nodes@);
    ret
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

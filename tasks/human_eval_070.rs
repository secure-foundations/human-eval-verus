/*
### ID
HumanEval/70
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// #[verifier::external_body]
// // Helper lemma to prove that swapping two elements doesn't change the multiset
// proof fn swap_preserves_multiset(s: Seq<int>, i: int, j: int)
//     requires 0 <= i < s.len() && 0 <= j < s.len()
//     ensures s.to_multiset() == s.update(i, s.index(j)).update(j, s.index(i)).to_multiset()
// {
//     let s_new = s.update(i, s.index(j)).update(j, s.index(i));
//     assert(s.to_multiset().count(s.index(i)) == s_new.to_multiset().count(s.index(i)));
//     assert(s.to_multiset().count(s.index(j)) == s_new.to_multiset().count(s.index(j)));
//     assert forall|x: int| s.to_multiset().count(x) == s_new.to_multiset().count(x) by {
//         if x != s.index(i) && x != s.index(j) {
//             assert(s.to_multiset().count(x) == s_new.to_multiset().count(x));
//         }
//     }
// }
fn sort_seq(s: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < ret@.len() ==> ret@.index(i) <= ret@.index(j),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
{
    let mut sorted = s.clone();
    let mut i: usize = 0;
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> sorted@.index(j) <= sorted@.index(k),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|j: int, k: int|
                0 <= j < i <= k < sorted@.len() ==> sorted@.index(j) <= sorted@.index(k),
            sorted@.len() == s@.len(),
    {
        let mut min_index: usize = i;
        let mut j: usize = i + 1;
        while j < sorted.len()
            invariant
                i <= min_index < j <= sorted.len(),
                forall|k: int| i <= k < j ==> sorted@.index(min_index as int) <= sorted@.index(k),
        {
            if sorted[j] < sorted[min_index] {
                min_index = j;
            }
            j += 1;
        }
        if min_index != i {
            let curr_val = sorted[i];
            let min_val = sorted[min_index];
            sorted.set(i, min_val);
            sorted.set(min_index, curr_val);
            proof {
                // swap_preserves_multiset(s@.map_values(|x| x as int), i as int, min_index as int);
                assume(s@.to_multiset() == sorted@.to_multiset());
            }
        }
        i += 1;
    }
    sorted
}

// returns (sorted, strange). Also returning sorted solely to have access to it for writing postcondition
fn strange_sort_list_helper(s: &Vec<i32>) -> (ret: (Vec<i32>, Vec<i32>))
    ensures
        s@.to_multiset() == (ret.0)@.to_multiset(),
        s@.len() == (ret.0)@.len() == (ret.1)@.len(),
        forall|i: int|
            0 <= i < s@.len() && i % 2 == 0 ==> (ret.1)@.index(i) == (ret.0)@.index(i / 2),
        forall|i: int|
            0 <= i < s@.len() && i % 2 == 1 ==> (ret.1)@.index(i) == (ret.0)@.index(
                s@.len() - (i - 1) / 2 - 1,
            ),
{
    let sorted = sort_seq(s);
    let mut strange = Vec::new();
    let mut i: usize = 0;
    while i < sorted.len()
        invariant
            i <= sorted.len() == s@.len(),
            strange@.len() == i,
            forall|j: int| 0 <= j < i && j % 2 == 0 ==> strange@.index(j) == sorted@.index(j / 2),
            forall|j: int|
                0 < j < i && j % 2 == 1 ==> strange@.index(j) == sorted@.index(
                    sorted@.len() - (j / 2) - 1,
                ),
    {
        if i % 2 == 0 {
            strange.push(sorted[i / 2]);
        } else {
            let r = (i - 1) / 2;
            strange.push(sorted[s.len() - r - 1]);
        }
        i += 1;
    }
    (sorted, strange)
}

fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        s@.len() == ret@.len(),
{
    let (_, strange) = strange_sort_list_helper(s);
    strange
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def strange_sort_list(lst):
    '''
    Given list of integers, return list in strange order.
    Strange sorting, is when you start with the minimum value,
    then maximum of the remaining integers, then minimum and so on.

    Examples:
    strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
    strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
    strange_sort_list([]) == []
    '''

*/

/*
### ENTRY POINT
strange_sort_list
*/

/*
### CANONICAL SOLUTION
    res, switch = [], True
    while lst:
        res.append(min(lst) if switch else max(lst))
        lst.remove(res[-1])
        switch = not switch
    return res

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4]) == [1, 4, 2, 3]
    assert candidate([5, 6, 7, 8, 9]) == [5, 9, 6, 8, 7]
    assert candidate([1, 2, 3, 4, 5]) == [1, 5, 2, 4, 3]
    assert candidate([5, 6, 7, 8, 9, 1]) == [1, 9, 5, 8, 6, 7]
    assert candidate([5, 5, 5, 5]) == [5, 5, 5, 5]
    assert candidate([]) == []
    assert candidate([1,2,3,4,5,6,7,8]) == [1, 8, 2, 7, 3, 6, 4, 5]
    assert candidate([0,2,2,2,5,5,-5,-5]) == [-5, 5, -5, 5, 0, 2, 2, 2]
    assert candidate([111111]) == [111111]

    # Check some edge cases that are easy to work out by hand.
    assert True


*/

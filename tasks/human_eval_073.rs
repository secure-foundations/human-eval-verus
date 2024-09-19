/*
### ID
HumanEval/73
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}

spec fn diff(s: Seq<(i32, i32)>) -> int {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}

fn smallest_change(v: Vec<i32>) -> (change: usize)
    requires
        v@.len() < usize::MAX,
    ensures
        change == diff(zip_halves(v@)),
{
    let mut ans: usize = 0;
    let ghost zipped = Seq::<(i32, i32)>::empty();
    for i in 0..v.len() / 2
        invariant
            ans <= i <= v@.len() / 2 < usize::MAX,
            ans == diff(zipped),
            zipped =~= zip_halves(v@).take(i as int),
    {
        proof {
            let ghost pair = (v[i as int], v[v.len() - i - 1]);
            let ghost zipped_old = zipped;
            zipped = zipped.push(pair);
            assert(zipped.drop_last() =~= zipped_old);
        }
        if v[i] != v[v.len() - i - 1] {
            ans += 1;
        }
    }
    assert(zip_halves(v@).take((v@.len() / 2) as int) =~= zip_halves(v@));
    ans
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def smallest_change(arr):
    """
    Given an array arr of integers, find the minimum number of elements that
    need to be changed to make the array palindromic. A palindromic array is an array that
    is read the same backwards and forwards. In one change, you can change one element to any other element.

    For example:
    smallest_change([1,2,3,5,4,7,9,6]) == 4
    smallest_change([1, 2, 3, 4, 3, 2, 2]) == 1
    smallest_change([1, 2, 3, 2, 1]) == 0
    """

*/

/*
### ENTRY POINT
smallest_change
*/

/*
### CANONICAL SOLUTION
    ans = 0
    for i in range(len(arr) // 2):
        if arr[i] != arr[len(arr) - i - 1]:
            ans += 1
    return ans

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,3,5,4,7,9,6]) == 4
    assert candidate([1, 2, 3, 4, 3, 2, 2]) == 1
    assert candidate([1, 4, 2]) == 1
    assert candidate([1, 4, 4, 2]) == 1

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1, 2, 3, 2, 1]) == 0
    assert candidate([3, 1, 1, 3]) == 0
    assert candidate([1]) == 0
    assert candidate([0, 1]) == 1


*/

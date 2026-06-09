/*
### ID
HumanEval/133
*/
/*
### VERUS BEGIN
*/
use std::mem::take;
use vstd::{arithmetic::overflow::CheckedU64, invariant, prelude::*};
use vstd::arithmetic::mul::lemma_mul_cancels_negatives;


verus! {

spec fn sum_squares_spec(arr: Seq<int>) -> int
    decreases arr.len(),
{
    if (arr.len() == 0) {
        0
    } else {
        (arr[0] * arr[0]) + sum_squares_spec(arr.drop_first())
    }
}

proof fn lemma_sum_squares_spec_concat(a1: Seq<int>, a2: Seq<int>)
    ensures
        sum_squares_spec(a1 + a2) == sum_squares_spec(a1) + sum_squares_spec(a2),
    decreases a1.len(),
{
    if (a1.len() == 0) {
        assert(sum_squares_spec(a1 + a2) == sum_squares_spec(a1) + sum_squares_spec(a2));
    } else {
        assert((a1 + a2).drop_first() == a1.drop_first() + a2);
        lemma_sum_squares_spec_concat(a1.drop_first(), a2);
    }
}

fn sum_squares(v: Vec<i32>) -> (out: Option<u64>)
    ensures
        ({
            let expected_sum = sum_squares_spec(v@.map_values(|x: i32| x as int));
            match out {
                Some(val) => val as int == expected_sum && expected_sum <= u64::MAX as int,
                None => expected_sum > u64::MAX as int,
            }
        }),
{
    let mut s: CheckedU64 = CheckedU64::new(0);
    let mut sq: CheckedU64 = CheckedU64::new(1);
    for i in 0..v.len()
        invariant
            sq@ as int == 1,
            s@ as int == sum_squares_spec(v@.take(i as int).map_values(|x: i32| x as int)),
    {
        let vi: u64 = if v[i] >= 0 {
            v[i] as u64
        } else {
            (-(v[i] as i64)) as u64
        };

        let stemp = sq.mul_value(vi);
        let stemp = stemp.mul_value(vi);
        s = s.add_checked(&stemp);

        assert(s@ as int == sum_squares_spec(v@.take((i + 1) as int).map_values(|x: i32| x as int)))
            by {
            let prev_slice = v@.take(i as int).map_values(|x: i32| x as int);
            let cur_slice = v@.take((i + 1) as int).map_values(|x: i32| x as int);
            let singleton_vi_seq = seq![cur_slice[i as int]];
            assert(prev_slice + singleton_vi_seq =~= cur_slice);
            lemma_sum_squares_spec_concat(prev_slice, singleton_vi_seq);
            reveal_with_fuel(sum_squares_spec, 2);
            if (v[i as int] < 0) {
                let val: int = v[i as int] as int;
                assert(val < 0);
                let v1: int = ((-(val as i64)) as u64) as int;
                let vx = v1;
                assert((v1 * v1) >= 0); // Tentative to trigger lemma automatically did not worked
                assert((v1 * v1) == (-v1) * (-v1) ) by {
                    lemma_mul_cancels_negatives(v1,v1);
                };
            }
        }
    };
    assert(v@.take(v.len() as int) == v@);
    return s.to_option();
}

fn static_checks() {
    let v = vec![2,3,-1,5];
    let r = sum_squares(v);

    assert(r.unwrap() == 39) by {
        let s: Seq<int> = seq![2, 3, -1, 5];
        assert(v@.map_values(|x: i32| x as int) == s);
        let s_res = sum_squares_spec(s);
        assert(s_res == 39) by {
            reveal_with_fuel(sum_squares_spec, 5);
            assert(s[0] * s[0] == 4);
            assert(s[1] * s[1] == 9);
            assert(s[2] * s[2] == 1);
            assert(s[3] * s[3] == 25);
        }
        let a = r.unwrap();
        assert(a == 39);
    };
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def sum_squares(lst):
    """You are given a list of numbers.
    You need to return the sum of squared numbers in the given list,
    round each element in the list to the upper int(Ceiling) first.
    Examples:
    For lst = [1,2,3] the output should be 14
    For lst = [1,4,9] the output should be 98
    For lst = [1,3,5,7] the output should be 84
    For lst = [1.4,4.2,0] the output should be 29
    For lst = [-2.4,1,1] the output should be 6


    """

*/

/*
### ENTRY POINT
sum_squares
*/

/*
### CANONICAL SOLUTION
    import math
    squared = 0
    for i in lst:
        squared += math.ceil(i)**2
    return squared

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,3])==14, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1.0,2,3])==14, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1,3,5,7])==84, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1.4,4.2,0])==29, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-2.4,1,1])==6, "This prints if this assert fails 1 (good for debugging!)"

    assert candidate([100,1,15,2])==10230, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([10000,10000])==200000000, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-1.4,4.6,6.3])==75, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([-1.4,17.9,18.9,19.9])==1086, "This prints if this assert fails 1 (good for debugging!)"


    # Check some edge cases that are easy to work out by hand.
    assert candidate([0])==0, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([-1])==1, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([-1,1,0])==2, "This prints if this assert fails 2 (also good for debugging!)"


*/

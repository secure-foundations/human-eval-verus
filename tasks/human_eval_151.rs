use std::mem::take;

/*
### ID
HumanEval/151
*/
/*
### VERUS BEGIN
*/
use vstd::{arithmetic::overflow::CheckedU64, invariant, prelude::*};

verus! {

spec fn double_the_difference_spec(arr: Seq<int>) -> int
    decreases arr.len(),
{
    if (arr.len() == 0) {
        0
    } else {
        if (arr[0] >= 0 && arr[0] % 2 == 1) {
            arr[0] * arr[0] + double_the_difference_spec(arr.drop_first())
        } else {
            double_the_difference_spec(arr.drop_first())
        }
    }
}

proof fn lemma_double_the_difference_spec_concat(a1: Seq<int>, a2: Seq<int>)
    ensures
        double_the_difference_spec(a1 + a2) == double_the_difference_spec(a1)
            + double_the_difference_spec(a2),
    decreases a1.len(),
{
    if (a1.len() == 0) {
        assert(double_the_difference_spec(a1 + a2) == double_the_difference_spec(a1)
            + double_the_difference_spec(a2));
    } else {
        assert((a1 + a2).drop_first() == a1.drop_first() + a2);
        lemma_double_the_difference_spec_concat(a1.drop_first(), a2);
    }
}

fn double_the_difference(v: Vec<i32>) -> (out: Option<u64>)
    ensures
        ({
            let expected_sum = double_the_difference_spec(v@.map_values(|x: i32| x as int));
            match out {
                Some(val) => val as int == expected_sum,
                None => expected_sum > u64::MAX as int,
            }
        }),
{
    let mut s: CheckedU64 = CheckedU64::new(0);
    let mut sq: CheckedU64 = CheckedU64::new(1);
    for i in 0..v.len()
        invariant
            sq@ as int == 1,
            s@ as int == double_the_difference_spec(
                v@.take(i as int).map_values(|x: i32| x as int),
            ),
    {
        if (v[i] > 0 && v[i] % 2 == 1) {
            let stemp = sq.mul_value(v[i] as u64);
            let stemp = stemp.mul_value(v[i] as u64);
            s = s.add_checked(&stemp);
        }
        assert(s@ as int == double_the_difference_spec(
            v@.take((i + 1) as int).map_values(|x: i32| x as int),
        )) by {
            let prev_slice = v@.take(i as int).map_values(|x: i32| x as int);
            let cur_slice = v@.take((i + 1) as int).map_values(|x: i32| x as int);
            let singleton_vi_seq = seq![cur_slice[i as int]];
            assert(prev_slice + singleton_vi_seq =~= cur_slice);
            lemma_double_the_difference_spec_concat(prev_slice, singleton_vi_seq);
            reveal_with_fuel(double_the_difference_spec, 2);
        };
    };
    assert(v@.take(v.len() as int) == v@);
    return s.to_option();
}

fn static_checks() {
    let v = vec![2,3,-1,5];
    let r = double_the_difference(v);

    assert(r.unwrap() == 34) by {
        let s: Seq<int> = seq![2, 3, -1, 5];
        assert(v@.map_values(|x: i32| x as int) == s);
        let s_res = double_the_difference_spec(s);
        assert(s_res == 34) by {
            reveal_with_fuel(double_the_difference_spec, 5);
            assert(s[0] * s[0] == 4);
            assert(s[1] * s[1] == 9);
            assert(s[2] * s[2] == 1);
            assert(s[3] * s[3] == 25);
        }
        let a = r.unwrap();
        assert(a == 34);
    };
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def double_the_difference(lst):
    '''
    Given a list of numbers, return the sum of squares of the numbers
    in the list that are odd. Ignore numbers that are negative or not integers.

    double_the_difference([1, 3, 2, 0]) == 1 + 9 + 0 + 0 = 10
    double_the_difference([-1, -2, 0]) == 0
    double_the_difference([9, -2]) == 81
    double_the_difference([0]) == 0

    If the input list is empty, return 0.
    '''

*/

/*
### ENTRY POINT
double_the_difference
*/

/*
### CANONICAL SOLUTION
    return sum([i**2 for i in lst if i > 0 and i%2!=0 and "." not in str(i)])

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([]) == 0 , "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([5, 4]) == 25 , "This prints if this assert fails 2 (good for debugging!)"
    assert candidate([0.1, 0.2, 0.3]) == 0 , "This prints if this assert fails 3 (good for debugging!)"
    assert candidate([-10, -20, -30]) == 0 , "This prints if this assert fails 4 (good for debugging!)"


    # Check some edge cases that are easy to work out by hand.
    assert candidate([-1, -2, 8]) == 0, "This prints if this assert fails 5 (also good for debugging!)"
    assert candidate([0.2, 3, 5]) == 34, "This prints if this assert fails 6 (also good for debugging!)"
    lst = list(range(-99, 100, 2))
    odd_sum = sum([i**2 for i in lst if i%2!=0 and i > 0])
    assert candidate(lst) == odd_sum , "This prints if this assert fails 7 (good for debugging!)"


*/

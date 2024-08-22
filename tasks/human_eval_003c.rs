/*
### ID
HumanEval/3
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// This function is part of the specification
pub open spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}

// This function is also part of the specification
pub open spec fn first_n(s: Seq<i32>, n: int) -> Seq<int> {
    s.take(n).map(|_idx, j: i32| j as int)
}

// This function is used by the proof
pub open spec fn sum_other_way(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s.last() + sum_other_way(s.drop_last())
    }
}

proof fn lemma_sum_equals_sum_other_way(s: Seq<int>)
    ensures
        sum(s) == sum_other_way(s),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(sum(s.skip(1)) == 0);
        assert(sum_other_way(s.drop_last()) == 0);
    } else if s.len() > 1 {
        let ss = s.skip(1);
        lemma_sum_equals_sum_other_way(ss);
        assert(sum_other_way(ss) == ss.last() + sum_other_way(ss.drop_last()));
        lemma_sum_equals_sum_other_way(ss.drop_last());
        assert(ss.drop_last() == s.drop_last().skip(1));
        lemma_sum_equals_sum_other_way(s.drop_last());
    }
}

fn below_zero(operations: Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && #[trigger] sum(first_n(operations@, i)) < 0,
{
    let mut s = 0i32;
    let mut num_overflows: usize = 0;
    let ghost max_plus = i32::MAX + 1;
    for k in 0..operations.len()
        invariant
            num_overflows <= k,
            max_plus == i32::MAX + 1,
            s >= 0,
            s + num_overflows * max_plus == sum(first_n(operations@, k as int)),
            forall|i: int| 0 <= i <= k ==> #[trigger] sum(first_n(operations@, i)) >= 0,
    {
        assert(sum(first_n(operations@, k as int)) + operations@[k as int] == sum(
            first_n(operations@, k + 1),
        )) by {
            let q1 = first_n(operations@, k as int);
            let q2 = first_n(operations@, k + 1);
            assert(q2.last() == operations@[k as int] as int);
            assert(q2.drop_last() == q1);
            lemma_sum_equals_sum_other_way(q1);
            lemma_sum_equals_sum_other_way(q2);
        }
        let op = operations[k];
        if op >= 0 {
            if s > i32::MAX - op {
                s += op - i32::MAX - 1;
                num_overflows += 1;
            } else {
                s += op;
            }
        } else {
            s += op;
            if s < 0 {
                if num_overflows == 0 {
                    return true;
                }
                num_overflows -= 1;
                s = s + i32::MAX + 1;
            }
        }
    }
    false
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def below_zero(operations: List[int]) -> bool:
    """ You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
    >>> below_zero([1, 2, 3])
    False
    >>> below_zero([1, 2, -4, 5])
    True
    """

*/

/*
### ENTRY POINT
below_zero
*/

/*
### CANONICAL SOLUTION
    balance = 0

    for op in operations:
        balance += op
        if balance < 0:
            return True

    return False

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == False
    assert candidate([1, 2, -3, 1, 2, -3]) == False
    assert candidate([1, 2, -4, 5, 6]) == True
    assert candidate([1, -1, 2, -2, 5, -5, 4, -4]) == False
    assert candidate([1, -1, 2, -2, 5, -5, 4, -5]) == True
    assert candidate([1, -2, 2, -2, 5, -5, 4, -4]) == True

*/

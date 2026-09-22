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
        s[0] + sum(s[1..])
    }
}

// This function is used by the proof
pub open spec fn sum_other_way(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s[..s.len() - 1])
    }
}

proof fn lemma_sum_equals_sum_other_way(s: Seq<int>)
    ensures
        sum(s) == sum_other_way(s),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(sum(s[1..]) == 0);
        assert(sum_other_way(s[..s.len() - 1]) == 0);
    } else if s.len() > 1 {
        let ss = s[1..];
        lemma_sum_equals_sum_other_way(ss);
        assert(sum_other_way(ss) == ss[ss.len() - 1] + sum_other_way(ss[..ss.len() - 1]));
        lemma_sum_equals_sum_other_way(ss[..ss.len() - 1]);
        assert(ss[..ss.len() - 1] == s[..s.len() - 1][1..]);
        lemma_sum_equals_sum_other_way(s[..s.len() - 1]);
    }
}

fn below_zero(operations: Vec<i32>) -> (result: bool)
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum((#[trigger] operations@[..i]).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum((#[trigger] operations@[..i]).map(|_idx, j: i32| j as int))
                < 0,
{
    let mut s = 0i32;
    for k in 0..operations.len()
        invariant
            s == sum(operations@[..k].map(|_idx, j: i32| j as int)),
            forall|i: int|
                0 <= i <= operations@.len() ==> sum(
                    (#[trigger] operations@[..i]).map(|_idx, j: i32| j as int),
                ) <= i32::MAX,
            forall|i: int|
                0 <= i <= k ==> sum((#[trigger] operations@[..i]).map(|_idx, j: i32| j as int)) >= 0,
    {
        assert(s + operations@[k as int] == sum(
            operations@[..k + 1].map(|_idx, j: i32| j as int),
        )) by {
            let q1 = operations@[..k].map(|_idx, j: i32| j as int);
            let q2 = operations@[..k + 1].map(|_idx, j: i32| j as int);
            assert(q2[q2.len() - 1] == operations@[k as int] as int);
            assert(q2[..q2.len() - 1] == q1);
            lemma_sum_equals_sum_other_way(q1);
            lemma_sum_equals_sum_other_way(q2);
        }
        s = s + operations[k];
        if s < 0 {
            return true;
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

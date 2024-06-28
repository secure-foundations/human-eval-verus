
/*
### ID
HumanEval/3
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s.last() + sum(s.drop_last())
    }
}

fn below_zero(operation: &[i64]) -> (r: bool)
    ensures
        r <==> (forall|i: int|
            0 <= i <= operation.len() ==> sum(#[trigger] operation@.subrange(0, i)) >= 0),
{
    // We use i128 since it allows us to have sufficiently large numbers without overflowing.
    let mut s = 0i128;
    for i in 0usize..operation.len()
        invariant
            s == sum(operation@.subrange(0, i as int)),
            forall|j: int| 0 <= j <= i ==> sum(#[trigger] operation@.subrange(0, j)) >= 0,
            i64::MIN <= s <= i64::MAX * i,
    {
        assert(operation@.subrange(0, i as int) =~= operation@.subrange(
            0,
            (i + 1) as int,
        ).drop_last());
        s = s + operation[i] as i128;
        if s < 0 {
            return false;
        }
    }
    true
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


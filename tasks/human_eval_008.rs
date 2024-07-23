/*
### ID
HumanEval/8
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::mul::*;
use vstd::calc;
use vstd::prelude::*;

verus! {

// proof and spec modified from human_eval_003a.rs
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

// This function is part of the specification
pub open spec fn product(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1
    } else {
        s[0] * product(s.skip(1))
    }
}

// This function is used by the proof
pub open spec fn sum_other_way(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}

// This function is used by the proof
proof fn lemma_sum_equals_sum_other_way(s: Seq<int>)
    ensures
        sum(s) == sum_other_way(s),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(sum(s.skip(1)) == 0);
        assert(sum_other_way(s.take(s.len() - 1)) == 0);
    } else if s.len() > 1 {
        let ss = s.skip(1);
        lemma_sum_equals_sum_other_way(ss);
        assert(sum_other_way(ss) == ss[ss.len() - 1] + sum_other_way(ss.take(ss.len() - 1)));
        lemma_sum_equals_sum_other_way(ss.take(ss.len() - 1));
        assert(ss.take(ss.len() - 1) == s.take(s.len() - 1).skip(1));
        lemma_sum_equals_sum_other_way(s.take(s.len() - 1));
    }
}

// This function is used by the proof
pub open spec fn prod_another_way(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1
    } else {
        s[s.len() - 1] * prod_another_way(s.take(s.len() - 1))
    }
}

// This function is used by the proof
proof fn lemma_prod_equals_prod_other_way(s: Seq<int>)
    ensures
        product(s) == prod_another_way(s),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(product(s.skip(1)) == 1);
        assert(s.take(s.len() - 1) == Seq::<int>::empty());
        assert(prod_another_way(Seq::<int>::empty()) == 1);
        assert(prod_another_way(s.take(s.len() - 1)) == 1);
    } else if s.len() > 1 {
        let ss = s.skip(1);
        lemma_prod_equals_prod_other_way(ss);
        lemma_prod_equals_prod_other_way(ss.take(ss.len() - 1));
        assert(ss.take(ss.len() - 1) == s.take(s.len() - 1).skip(1));
        lemma_prod_equals_prod_other_way(s.take(s.len() - 1));

        broadcast use lemma_mul_is_commutative;
        broadcast use lemma_mul_is_associative;

    }
}

fn sum_product(numbers: Vec<i32>) -> (ret: (i32, i32))
    requires
        forall|i: int|
            #![trigger numbers@.take(i)]
            0 <= i <= numbers@.len() ==> i32::MIN <= sum(
                numbers@.take(i).map(|_idx, j: i32| j as int),
            ) <= i32::MAX,
        forall|i: int|
            #![trigger numbers@.take(i)]
            0 <= i <= numbers@.len() ==> i32::MIN <= product(
                numbers@.take(i).map(|_idx, j: i32| j as int),
            ) <= i32::MAX,
    ensures
        ret.0 == sum(numbers@.map(|_idx, j: i32| j as int)),
        ret.1 == product(numbers@.map(|_idx, j: i32| j as int)),
{
    let mut p = 1i32;
    let mut s = 0i32;

    for k in 0..numbers.len()
        invariant
            s == sum(numbers@.take(k as int).map(|_idx, j: i32| j as int)),
            forall|i: int|
                #![trigger numbers@.take(i)]
                0 <= i <= numbers@.len() ==> i32::MIN <= sum(
                    numbers@.take(i).map(|_idx, j: i32| j as int),
                ) <= i32::MAX,
            p == product(numbers@.take(k as int).map(|_idx, j: i32| j as int)),
            forall|i: int|
                #![trigger numbers@.take(i)]
                0 <= i <= numbers@.len() ==> i32::MIN <= product(
                    numbers@.take(i).map(|_idx, j: i32| j as int),
                ) <= i32::MAX,
    {
        assert(s + numbers@[k as int] == sum(numbers@.take(k + 1).map(|_idx, j: i32| j as int)))
            by {
            let q1 = numbers@.take(k as int).map(|_idx, j: i32| j as int);
            let q2 = numbers@.take(k + 1).map(|_idx, j: i32| j as int);
            assert(q2[q2.len() - 1] == numbers@[k as int] as int);
            assert(q2.take(q2.len() - 1) == q1);
            lemma_sum_equals_sum_other_way(q1);
            lemma_sum_equals_sum_other_way(q2);
        }
        assert(p * numbers@[k as int] == product(numbers@.take(k + 1).map(|_idx, j: i32| j as int)))
            by {
            let q1 = numbers@.take(k as int).map(|_idx, j: i32| j as int);
            let q2 = numbers@.take(k + 1).map(|_idx, j: i32| j as int);
            assert(q2[q2.len() - 1] == numbers@[k as int] as int);
            assert(q2.take(q2.len() - 1) == q1);
            lemma_prod_equals_prod_other_way(q1);
            lemma_prod_equals_prod_other_way(q2);
            assert(p * q2[q2.len() - 1] == product(q2)) by {
                // expand definition of product(q2)
                assert(product(q2) == q2[q2.len() - 1] * prod_another_way(q2.take(q2.len() - 1)));
            };
        }
        s = s + numbers[k];
        p = p * numbers[k];
    }
    assert(s == sum(numbers@.take(numbers.len() as int).map(|_idx, j: i32| j as int)));
    assert(numbers@.take(numbers.len() as int) == numbers@);
    (s, p)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List, Tuple


def sum_product(numbers: List[int]) -> Tuple[int, int]:
    """ For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
    Empty sum should be equal to 0 and empty product should be equal to 1.
    >>> sum_product([])
    (0, 1)
    >>> sum_product([1, 2, 3, 4])
    (10, 24)
    """

*/

/*
### ENTRY POINT
sum_product
*/

/*
### CANONICAL SOLUTION
    sum_value = 0
    prod_value = 1

    for n in numbers:
        sum_value += n
        prod_value *= n
    return sum_value, prod_value

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == (0, 1)
    assert candidate([1, 1, 1]) == (3, 1)
    assert candidate([100, 0]) == (100, 0)
    assert candidate([3, 5, 7]) == (3 + 5 + 7, 3 * 5 * 7)
    assert candidate([10]) == (10, 10)

*/

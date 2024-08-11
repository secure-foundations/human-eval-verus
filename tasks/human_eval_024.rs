/*
### ID
HumanEval/24
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse_div,
};
use vstd::prelude::*;

verus! {

pub open spec fn mul(a: nat, b: nat) -> nat {
    builtin::mul(a, b)
}

/// Specification for what it means for d to divide a
pub open spec fn divides(v: nat, d: nat) -> bool {
    exists|k: nat| mul(d, k) == v
}

/// Helper function to prove a % b == 0 imples b divides a
proof fn lemma_mod_zero(a: nat, b: nat)
    requires
        a > 0 && b > 0,
        a % b == 0,
    ensures
        divides(a, b),
{
    lemma_fundamental_div_mod(a as int, b as int);
    assert(mul(b, (a / b)) == a);
}

/// Helper function to prove b divides a imples a % b == 0
proof fn lemma_mod_zero_reversed(a: nat, b: nat)
    requires
        a > 0 && b > 0,
        divides(a, b),
    ensures
        a % b == 0,
{
    let k_wit = choose|k: nat| mul(b, k) == a;
    assert(k_wit == a / b) by {
        lemma_fundamental_div_mod_converse_div(a as int, b as int, k_wit as int, 0 as int);
    }
    lemma_fundamental_div_mod(a as int, b as int);
}

/// Helper function to prove everything is divided by one
proof fn lemma_one_divides_all()
    ensures
        forall|v: nat| divides(v, 1 as nat),
{
    assert forall|v: nat| divides(v, 1 as nat) by {
        assert(mul(1 as nat, v) == v);
    }
}

/// Implementation.
fn largest_divisor(n: u32) -> (ret: u32)
    requires
        n > 1,
    ensures
        divides(n as nat, ret as nat),
        ret < n,
        forall|k: u32| (0 < k < n && divides(n as nat, k as nat)) ==> ret >= k,
{
    let mut i = n - 1;
    while i >= 2
        invariant
            n > 0,
            i < n,
            forall|k: u32| i < k < n ==> !divides(n as nat, k as nat),
    {
        if n % i == 0 {
            assert(divides(n as nat, i as nat)) by {
                lemma_mod_zero(n as nat, i as nat);
            }
            return i;
        }
        i -= 1;

        assert forall|k: u32| i < k < n implies !divides(n as nat, k as nat) by {
            if k == i + 1 {
                assert(!divides(n as nat, k as nat)) by {
                    if (divides(n as nat, k as nat)) {
                        lemma_mod_zero_reversed(n as nat, k as nat);
                    }
                }
            }
        }
    }
    assert(divides(n as nat, 1 as nat)) by {
        lemma_one_divides_all();
    }
    1
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def largest_divisor(n: int) -> int:
    """ For a given number n, find the largest number that divides n evenly, smaller than n
    >>> largest_divisor(15)
    5
    """

*/

/*
### ENTRY POINT
largest_divisor
*/

/*
### CANONICAL SOLUTION
    for i in reversed(range(n)):
        if n % i == 0:
            return i

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3) == 1
    assert candidate(7) == 1
    assert candidate(10) == 5
    assert candidate(100) == 50
    assert candidate(49) == 7

*/

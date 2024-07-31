/*
### ID
HumanEval/13
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

// TODO: Put your solution (the specification, implementation, and proof) to the task here
verus! {

pub open spec fn mul(a: nat, b: nat) -> nat {
    builtin::mul(a, b)
}

pub open spec fn divides(v: nat, d: nat) -> bool {
    exists|k: nat| mul(d, k) == v
}

pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    recommends
        a > 0 && b > 0,
    decreases a + b,
    via gcd_spec_dec
{
    if a == b {
        a
    } else if a < b {
        gcd_spec(a, (b - a) as nat)
    } else {
        gcd_spec((a - b) as nat, b)
    }
}

#[via_fn]
proof fn gcd_spec_dec(a: nat, b: nat) {
    // TODO, why >= here can't work
    assume(a + b > a + ((b - a) as nat));
}

#[verifier::nonlinear]
proof fn helper(a: nat, b: nat, k: nat)
    requires
        a > 0 && b > 0 && k > 0,
        divides(k, a) && divides(k, b),
        b >= a,
    ensures
        exists|m: nat, n: nat| a == mul(m, k) && b == mul(n, k) && m <= n,
{
    let m_witness = choose|m: nat| #![trigger mul(m, k)] exists|k: nat| mul(m, k) == a;
    assume(mul(m_witness, k) == a);
    // TODO: triggers??
    let n_witness = choose|n: nat| #![trigger mul(n, k)] exists|k: nat| mul(n, k) == b;
    if m_witness <= n_witness {
        assert(a == mul(m_witness, k) && b == mul(n_witness, k) && m_witness <= n_witness);

        assert(exists|m: nat, n: nat| a == mul(m, k) && b == mul(n, k) && m <= n);
    } else {
        assume(false);
    }
}

fn greatest_common_divisor(a: u32, b: u32) -> (result: u32)
    requires
        a > 0 && b > 0,
    ensures
        divides(result as nat, a as nat) && divides(result as nat, b as nat),
        forall|x: nat| divides(x, a as nat) && divides(x, b as nat) ==> divides(x, result as nat),
{
    assume(false);
    if a == b {
        a
    } else if a < b {
        greatest_common_divisor(a, b - a)
    } else {
        greatest_common_divisor(a - b, b)
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def greatest_common_divisor(a: int, b: int) -> int:
    """ Return a greatest common divisor of two integers a and b
    >>> greatest_common_divisor(3, 5)
    1
    >>> greatest_common_divisor(25, 15)
    5
    """

*/

/*
### ENTRY POINT
greatest_common_divisor
*/

/*
### CANONICAL SOLUTION
    while b:
        a, b = b, a % b
    return a

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3, 7) == 1
    assert candidate(10, 15) == 5
    assert candidate(49, 14) == 7
    assert candidate(144, 60) == 12

*/

/*
### ID
HumanEval/49
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn modp_rec(n: nat, p: nat) -> nat
    decreases n,
{
    if n == 0 {
        1nat % p
    } else {
        (modp_rec((n - 1) as nat, p) * 2) % p
    }
}

fn modmul(a: u32, b: u32, p: u32) -> (mul: u32)
    by (nonlinear_arith)
    requires
        p > 0,
    ensures
        mul == ((a as int) * (b as int)) % (p as int),
{
    (((a as u64) * (b as u64)) % (p as u64)) as u32
}

#[verifier::loop_isolation(false)]
fn modp(n: u32, p: u32) -> (r: u32)
    by (nonlinear_arith)
    requires
        p > 0,
    ensures
        r == modp_rec(n as nat, p as nat),
{
    let mut r = 1u32 % p;
    for i in 0..n
        invariant
            r == modp_rec(i as nat, p as nat),
    {
        r = modmul(r, 2, p);
    }
    r
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def modp(n: int, p: int):
    """Return 2^n modulo p (be aware of numerics).
    >>> modp(3, 5)
    3
    >>> modp(1101, 101)
    2
    >>> modp(0, 101)
    1
    >>> modp(3, 11)
    8
    >>> modp(100, 101)
    1
    """

*/

/*
### ENTRY POINT
modp
*/

/*
### CANONICAL SOLUTION
    ret = 1
    for i in range(n):
        ret = (2 * ret) % p
    return ret

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(3, 5) == 3
    assert candidate(1101, 101) == 2
    assert candidate(0, 101) == 1
    assert candidate(3, 11) == 8
    assert candidate(100, 101) == 1
    assert candidate(30, 5) == 4
    assert candidate(31, 5) == 3


*/

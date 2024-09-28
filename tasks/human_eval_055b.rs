/*
### ID
HumanEval/55
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// O(n) non-recursive solution using same spec as 55a

#[verifier::memoize]
spec fn spec_fib(n: nat) -> nat
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}

proof fn lemma_fib_monotonic(i:nat, j:nat)
    requires
        i <= j
    ensures
        spec_fib(i) <= spec_fib(j),
    decreases j - i,
{
    if (i < 2 && j < 2) || i == j {
    } else if i == j - 1 {
        reveal_with_fuel(spec_fib, 2);
        lemma_fib_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fib_monotonic(i, (j - 1) as nat);
        lemma_fib_monotonic(i, (j - 2) as nat);
    }
}

fn fib(n: u32) -> (ret: Option<u32>)
    ensures
        match ret {
            None => spec_fib(n as nat) > u32::MAX,
            Some(f) => f == spec_fib(n as nat)
        },
{
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }
    if n > 47 {
        proof {
            assert(spec_fib(48) > u32::MAX) by (compute_only);
            lemma_fib_monotonic(48, n as nat);
        }
        return None;
    }
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 2;

    for i in 1..n
        invariant
            1 <= i as int <= n <= 47,
            a as int == spec_fib((i - 1) as nat),
            b as int == spec_fib(i as nat),
    {
        proof {
            // Prove that that n1 + n2 won't overflow
            assert(spec_fib(47) < u32::MAX) by (compute_only);
            lemma_fib_monotonic(i as nat, 47);
            lemma_fib_monotonic((i - 1) as nat, 47);
            lemma_fib_monotonic((i + 1) as nat, 47);
        }
        let sum = a + b;
        a = b;
        b = sum;
    }
    Some(b)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def fib(n: int):
    """Return n-th Fibonacci number.
    >>> fib(10)
    55
    >>> fib(1)
    1
    >>> fib(8)
    21
    """

*/

/*
### ENTRY POINT
fib
*/

/*
### CANONICAL SOLUTION
    if n == 0:
        return 0
    if n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(10) == 55
    assert candidate(1) == 1
    assert candidate(8) == 21
    assert candidate(11) == 89
    assert candidate(12) == 144


*/

/*
### ID
HumanEval/55
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

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

proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires
        i <= j,
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
            Some(f) => f == spec_fib(n as nat),
        },
    decreases n,
{
    if n > 47 {
        proof {
            assert(spec_fib(48) > u32::MAX) by (compute_only);
            lemma_fib_monotonic(48, n as nat);
        }
        return None;
    }
    match n {
        0 => Some(0),
        1 => Some(1),
        _ => {
            proof {
                // Prove that the recursive calls below succeed,
                // and that n1 + n2 won't overflow
                assert(spec_fib(47) < u32::MAX) by (compute_only);
                lemma_fib_monotonic(n as nat, 47);
                lemma_fib_monotonic((n - 1) as nat, 47);
                lemma_fib_monotonic((n - 2) as nat, 47);
            }
            let n1 = fib(n - 1)?;
            let n2 = fib(n - 2)?;
            Some(n1 + n2)
        },
    }
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

/*
### ID
HumanEval/46
*/
/*
### VERUS BEGIN
*/
use vstd::{invariant, prelude::*};

verus! {

proof fn lemma_fib4_n70_does_not_overflow()
    ensures
        fib4_spec(70) <= u64::MAX,
{
    // fib4_spec need to be memoize for computation to go through
    assert(fib4_spec(70) <= u64::MAX) by (compute_only);
}

proof fn lemma_fib4_is_monotomic_after_inc_4(n: nat)
    ensures
        (n > 3) ==> (fib4_spec(n) <= fib4_spec(n + 1)),
    decreases n,
{
    if (n <= 3) {
    } else {
        lemma_fib4_is_monotomic_after_inc_4((n - 1) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n - 2) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n - 3) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n - 4) as nat);
    }

}

#[verifier::memoize]
spec fn fib4_spec(n: nat) -> (out: nat)
    decreases n,
{
    match n {
        x if x <= 0 => 0,
        x if x == 1 => 0,
        x if x == 2 => 2,
        x if x == 3 => 0,
        _ => fib4_spec((n - 1) as nat) + fib4_spec((n - 2) as nat) + fib4_spec((n - 3) as nat)
            + fib4_spec((n - 4) as nat),
    }
}

proof fn lemma_fib4_monotonic_transitive(a: nat, b: nat)
    requires
        3 <= a <= b,
    ensures
        fib4_spec(a) <= fib4_spec(b),
    decreases b - a,
{
    if a < b {
        lemma_fib4_is_monotomic_after_inc_4(a);
        lemma_fib4_monotonic_transitive((a + 1) as nat, b);
    }
}

fn fib4(n: u32) -> (out: u64)
    requires
        n <= 70,
    ensures
        out == fib4_spec(n as nat),
{
    match n {
        x if x <= 0 => return 0,
        x if x == 1 => return 0,
        x if x == 2 => return 2,
        x if x == 3 => return 0,
        _ => 0,
    };

    let mut x0 = 0;
    let mut x1 = 0;
    let mut x2 = 2;
    let mut x3 = 0;
    let mut i = 3;

    while (i < n)
        invariant
            x3 == fib4_spec(i as nat),
            x2 == fib4_spec((i - 1) as nat),
            x1 == fib4_spec((i - 2) as nat),
            x0 == fib4_spec((i - 3) as nat),
            3 <= i <= n <= 70,
        decreases n - i,
    {
        let x3p = x3;
        proof {
            lemma_fib4_n70_does_not_overflow();
            lemma_fib4_monotonic_transitive((i + 1) as nat, 70);
        }

        x3 = x3 + x2 + x1 + x0;

        x0 = x1;
        x1 = x2;
        x2 = x3p;
        i += 1;
    }
    return x3;

}

// TODO: Put your solution (the specification, implementation, and proof) to the task here
fn static_checks() {
    reveal_with_fuel(fib4_spec, 8);

    let x = fib4(5);
    assert(x == 4);

    let x = fib4(8);
    assert(x == 28);
}

} // verus!
fn main() {
    assert!(fib4(5) == 4);
    assert!(fib4(8) == 28);
    assert!(fib4(10) == 104);
    assert!(fib4(12) == 386);
}

/*
### VERUS END
*/

/*
### PROMPT


def fib4(n: int):
    """The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fib4(0) -> 0
    fib4(1) -> 0
    fib4(2) -> 2
    fib4(3) -> 0
    fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
    Please write a function to efficiently compute the n-th element of the fib4 number sequence.  Do not use recursion.
    >>> fib4(5)
    4
    >>> fib4(6)
    8
    >>> fib4(7)
    14
    """

*/

/*
### ENTRY POINT
fib4
*/

/*
### CANONICAL SOLUTION
    results = [0, 0, 2, 0]
    if n < 4:
        return results[n]

    for _ in range(4, n + 1):
        results.append(results[-1] + results[-2] + results[-3] + results[-4])
        results.pop(0)

    return results[-1]

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(5) == 4
    assert candidate(8) == 28
    assert candidate(10) == 104
    assert candidate(12) == 386


*/

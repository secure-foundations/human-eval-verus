/*
### ID
HumanEval/139
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

// specification
pub closed spec fn factorial(n: nat) -> nat
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}

pub closed spec fn brazilian_factorial(n: nat) -> nat
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}

proof fn lemma_factorial_positive(n: nat)
    ensures
        factorial(n) >= 1,
    decreases n,
{
    if (n == 0) {
    } else {
        lemma_factorial_positive((n - 1) as nat);
        assert(factorial(n) >= 1) by {
            broadcast use lemma_mul_strictly_positive;

        };
    }
}

proof fn lemma_brazilian_factorial_positive(n: nat)
    ensures
        brazilian_factorial(n) >= 1,
    decreases n,
{
    if (n == 0) {
    } else {
        lemma_factorial_positive((n) as nat);
        lemma_brazilian_factorial_positive((n - 1) as nat);
        assert(brazilian_factorial(n) >= 1) by {
            lemma_mul_strictly_positive(
                factorial(n) as int,
                brazilian_factorial((n - 1) as nat) as int,
            )
        };
    }
}

proof fn lemma_brazilian_fib_monotonic(i: nat, j: nat)
    requires
        0 <= i <= j,
    ensures
        brazilian_factorial(i) <= brazilian_factorial(j),
    decreases j - i,
{
    if (i == j) {
    } else if (j == i + 1) {
        assert(factorial(j) >= 1) by { lemma_factorial_positive(j) };
        assert(brazilian_factorial(j) >= brazilian_factorial(i)) by {
            broadcast use lemma_mul_increases;

        };
    } else {
        lemma_brazilian_fib_monotonic(i, (j - 1) as nat);
        lemma_brazilian_fib_monotonic((j - 1) as nat, j);
    }
}

pub fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
{
    if n >= 9 {
        assert(brazilian_factorial(9nat) > u64::MAX) by (compute_only);
        assert(brazilian_factorial(n as nat) >= brazilian_factorial(9nat)) by {
            lemma_brazilian_fib_monotonic(9nat, n as nat)
        };
        return None;
    }
    let mut start = 1u64;
    let mut end = n + 1u64;
    let mut fact_i = 1u64;
    let mut special_fact = 1u64;

    while start < end
        invariant
            brazilian_factorial((start - 1) as nat) == special_fact,
            factorial((start - 1) as nat) == fact_i,
            1 <= start <= end < 10,
        decreases (end - start),
    {
        assert(brazilian_factorial(start as nat) <= brazilian_factorial(8nat)) by {
            lemma_brazilian_fib_monotonic(start as nat, 8nat)
        };
        assert(brazilian_factorial(8nat) < u64::MAX) by (compute_only);

        assert(brazilian_factorial((start - 1) as nat) >= 1) by {
            lemma_brazilian_factorial_positive((start - 1) as nat)
        };
        assert(factorial(start as nat) <= brazilian_factorial(start as nat)) by {
            broadcast use lemma_mul_ordering;

        };

        fact_i = start * fact_i;

        special_fact = fact_i * special_fact;

        start = start + 1;
    }
    return Some(special_fact);

}

} // verus!
fn main() {
    println!("{:?}", brazilian_factorial_impl(4));
    // > 288
    println!("{:?}", brazilian_factorial_impl(6));
    // > 24883200
}

/*
### VERUS END
*/

/*
### PROMPT

def special_factorial(n):
    """The Brazilian factorial is defined as:
    brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
    where n > 0

    For example:
    >>> special_factorial(4)
    288

    The function will receive an integer as input and should return the special
    factorial of this integer.
    """

*/

/*
### ENTRY POINT
special_factorial
*/

/*
### CANONICAL SOLUTION
    fact_i = 1
    special_fact = 1
    for i in range(1, n+1):
        fact_i *= i
        special_fact *= fact_i
    return special_fact

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(4) == 288, "Test 4"
    assert candidate(5) == 34560, "Test 5"
    assert candidate(7) == 125411328000, "Test 7"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1) == 1, "Test 1"


*/

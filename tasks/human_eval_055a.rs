/*
### ID
HumanEval/55
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

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

fn fib(n: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> ret.unwrap() == spec_fib(n as nat),
{
    match n {
        0 => Some(0),
        1 => Some(1),
        _ => {
            let n1 = fib(n - 1)?;
            let n2 = fib(n - 2)?;
            n1.checked_add(n2)
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

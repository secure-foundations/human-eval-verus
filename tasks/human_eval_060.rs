/*
### ID
HumanEval/60
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_sum_to_n(n: nat) -> nat
    decreases n,
{
    if (n == 0) {
        0
    } else {
        n + spec_sum_to_n((n - 1) as nat)
    }
}

proof fn lemma_sum_monotonic(i:nat, j:nat)
    requires
        i <= j
    ensures
        spec_sum_to_n(i) <= spec_sum_to_n(j),
    decreases j - i,
{
    if (i == 0 && j == 0) || i == j {
    } else if i == j - 1 {
        lemma_sum_monotonic(i, (j - 1) as nat);
    } else {
        lemma_sum_monotonic(i, (j - 1) as nat);
    }
}

fn sum_to_n(n: u32) -> (sum: Option<u32>)
    ensures
        match sum {
            None => spec_sum_to_n(n as nat) > u32::MAX,
            Some(f) => f == spec_sum_to_n(n as nat)
        },
{
    if n >= 92682 {
        proof {
            assert(spec_sum_to_n(92682) > u32::MAX) by (compute_only);
            lemma_sum_monotonic(92682, n as nat);
        }
        return None;
    }
    let mut res: u32 = 0;
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n < 92682,
            res == spec_sum_to_n(i as nat),
            res <= u32::MAX,
    {
        i += 1;
        proof {
            // Prove that that n1 + n2 won't overflow
            assert(spec_sum_to_n(92681) < u32::MAX) by (compute_only);
            lemma_sum_monotonic(i as nat, 92681);
            lemma_sum_monotonic((i - 1) as nat, 92681);
        }
        res = i + res;
    }
    Some(res)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def sum_to_n(n: int):
    """sum_to_n is a function that sums numbers from 1 to n.
    >>> sum_to_n(30)
    465
    >>> sum_to_n(100)
    5050
    >>> sum_to_n(5)
    15
    >>> sum_to_n(10)
    55
    >>> sum_to_n(1)
    1
    """

*/

/*
### ENTRY POINT
sum_to_n
*/

/*
### CANONICAL SOLUTION
    return sum(range(n + 1))

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(1) == 1
    assert candidate(6) == 21
    assert candidate(11) == 66
    assert candidate(30) == 465
    assert candidate(100) == 5050


*/

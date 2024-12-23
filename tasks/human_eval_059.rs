/*
### ID
HumanEval/59
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// Note that according to the canonical solution 1 is treated as a possible largest prime. We'll stick to this
spec fn spec_prime_helper(num: int, limit: int) -> bool {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}

spec fn spec_prime(num: int) -> bool {
    spec_prime_helper(num, num)
}

fn is_prime(num: u32) -> (result: bool)
    requires
        num >= 2,
    ensures
        result <==> spec_prime(num as int),
{
    let mut i = 2;
    let mut result = true;
    while i < num
        invariant
            2 <= i <= num,
            result <==> spec_prime_helper(num as int, i as int),
    {
        if num % i == 0 {
            result = false;
        }
        i += 1;
    }
    result
}

fn largest_prime_factor(n: u32) -> (largest: u32)
    requires
        n >= 2,
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
        n % largest == 0,
        forall|p| 0 <= p < n && spec_prime(p) && n as int % p == 0 ==> p <= largest,
{
    let mut largest = 1;
    let mut j = 1;
    while j < n
        invariant
            1 <= largest <= j <= n,
            spec_prime(largest as int),
            n % largest == 0,
            forall|p| 0 <= p <= j && spec_prime(p) && n as int % p == 0 ==> p <= largest,
    {
        j += 1;
        let flag = is_prime(j);
        if n % j == 0 && flag {
            largest =
            if largest > j {
                largest
            } else {
                j
            };
        }
    }
    largest
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def largest_prime_factor(n: int):
    """Return the largest prime factor of n. Assume n > 1 and is not a prime.
    >>> largest_prime_factor(13195)
    29
    >>> largest_prime_factor(2048)
    2
    """

*/

/*
### ENTRY POINT
largest_prime_factor
*/

/*
### CANONICAL SOLUTION
    def is_prime(k):
        if k < 2:
            return False
        for i in range(2, k - 1):
            if k % i == 0:
                return False
        return True
    largest = 1
    for j in range(2, n + 1):
        if n % j == 0 and is_prime(j):
            largest = max(largest, j)
    return largest

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(15) == 5
    assert candidate(27) == 3
    assert candidate(63) == 7
    assert candidate(330) == 11
    assert candidate(13195) == 29


*/

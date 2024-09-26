/*
### ID
HumanEval/31
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// specification
pub closed spec fn prime_helper(n: nat, k: nat) -> bool
    recommends
        2 <= k <= n,
    decreases n - k,
{
    if k < 2 || k > n {
        false  //arbitrarily chosen return value, should have 2 <= k <= n

    } else if n >= k >= n - 1 {
        true
    } else if n % k == 0 {
        false
    } else {
        prime_helper(n, k + 1)
    }
}

pub open spec fn is_prime(n: nat) -> bool {
    if n < 2 {
        false
    } else {
        prime_helper(n, 2)
    }
}

proof fn sanity_check() {
    assert(is_prime(6) == false) by (compute);
    assert(is_prime(101) == true) by (compute);
    assert(is_prime(11) == true) by (compute);
    assert(is_prime(13441) == true) by (compute);
    assert(is_prime(61) == true) by (compute);
    assert(is_prime(4) == false) by (compute);
    assert(is_prime(1) == false) by (compute);
}

// implementation
fn is_prime_impl(n: u8) -> (res: bool)
    ensures
        res == is_prime(n as nat),
{
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    let mut k = n - 1;
    let mut res = true;
    while (k > 2)
        invariant
            2 <= k <= n - 1,
            res == prime_helper(n as nat, k as nat),
    {
        k = k - 1;
        if n % k == 0 {
            res = false;
        }
    }
    return res;
}

} // verus!
fn main() {
    print!("6 is prime? {}\n", is_prime_impl(6));
    print!("101 is prime? {}\n", is_prime_impl(101));
    print!("11 is prime? {}\n", is_prime_impl(11));
    print!("61 is prime? {}\n", is_prime_impl(61));
    print!("4 is prime? {}\n", is_prime_impl(4));
    print!("1 is prime? {}\n", is_prime_impl(1));
}

/*
### VERUS END
*/

/*
### PROMPT


def is_prime(n):
    """Return true if a given number is prime, and false otherwise.
    >>> is_prime(6)
    False
    >>> is_prime(101)
    True
    >>> is_prime(11)
    True
    >>> is_prime(13441)
    True
    >>> is_prime(61)
    True
    >>> is_prime(4)
    False
    >>> is_prime(1)
    False
    """

*/

/*
### ENTRY POINT
is_prime
*/

/*
### CANONICAL SOLUTION
    if n < 2:
        return False
    for k in range(2, n - 1):
        if n % k == 0:
            return False
    return True

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(6) == False
    assert candidate(101) == True
    assert candidate(11) == True
    assert candidate(13441) == True
    assert candidate(61) == True
    assert candidate(4) == False
    assert candidate(1) == False
    assert candidate(5) == True
    assert candidate(11) == True
    assert candidate(17) == True
    assert candidate(5 * 17) == False
    assert candidate(11 * 7) == False
    assert candidate(13441 * 19) == False


*/

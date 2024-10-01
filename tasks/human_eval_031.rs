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
pub closed spec fn is_prime_so_far(n: nat, k: nat) -> bool
    recommends
        n > 1,
{
    forall|i| 1 < i < k ==> #[trigger] (n % i) != 0
}

pub open spec fn is_prime(n: nat) -> bool {
    (n > 1) && forall|i| 1 < i < n ==> #[trigger] (n % i) != 0
}

// proof fn sanity_check() {
//     assert(is_prime(6) == false) by (compute);
//     assert(is_prime(101) == true) by (compute);
//     assert(is_prime(11) == true) by (compute);
//     assert(is_prime(13441) == true) by (compute);
//     assert(is_prime(61) == true) by (compute);
//     assert(is_prime(4) == false) by (compute);
//     assert(is_prime(1) == false) by (compute);
// }

// implementation
fn is_prime_impl(n: u8) -> (res: bool)
    ensures
        res == is_prime(n as nat),
{
    if n < 2 {
        return false;
    }
    let mut k = 2;
    let mut res = true;

    while (k < n)
        invariant
            2 <= k <= n,
            res == is_prime_so_far(n as nat, k as nat),
    {
        assert((is_prime_so_far(n as nat, k as nat) && (n as nat) % (k as nat) != 0)
            == is_prime_so_far(n as nat, (k + 1) as nat));

        res = res && n % k != 0;
        k = k + 1;
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

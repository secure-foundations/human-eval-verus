/*
### ID
HumanEval/96
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn tdiv(n: nat, k: nat) -> (r: nat) {
    n % k
}

spec fn is_prime(n: nat) -> bool {
    if (n == 0 || n == 1) {
        false
    } else {
        !(exists|k: nat| (2 <= k < n) && (tdiv(n, k) == 0))
    }
}

spec fn primes_bellow(n: nat) -> Seq<nat>
    decreases n,
{
    if n <= 2 {
        seq![]
    } else {
        let prev = primes_bellow((n - 1) as nat);
        if is_prime((n - 1) as nat) {
            prev + seq![(n - 1) as nat]
        } else {
            prev
        }
    }
}

fn check_prime(p: i32) -> (o: bool)
    requires
        p >= 0,
    ensures
        o == is_prime(p as nat),
{
    if (p == 0 || p == 1 || p < 0) {
        return false;
    }
    let mut o = true;
    let mut possible_divisor = p - 1;
    let mut has_divisors = false;

    while (possible_divisor > 1)
        invariant
            0 <= possible_divisor <= p - 1,
            forall|k: nat|
                0 <= possible_divisor < k <= p - 1 ==> !(#[trigger] tdiv(p as nat, k as nat) == 0),
        decreases possible_divisor,
    {
        if (p % possible_divisor == 0) {
            assert(!is_prime(p as nat)) by {
                assert(tdiv(p as nat, possible_divisor as nat) == 0);
            }
            return false;
        }
        possible_divisor -= 1;
    }
    true
}

fn count_up_to(n: i32) -> (r: Vec<i32>)
    requires
        n >= 0,
    ensures
        primes_bellow(n as nat) == r@.map_values(|x| x as nat),
{
    let mut r: Vec<i32> = Vec::new();
    if (n == 0 || n == 1) {
        return r;
    }
    let mut possible_prime = 2;
    while (possible_prime < n)
        invariant
            2 <= possible_prime <= n,
            primes_bellow(possible_prime as nat) == r@.map_values(|x| x as nat),
        decreases n - possible_prime,
    {
        if (check_prime(possible_prime)) {
            r.push(possible_prime);
        }
        possible_prime += 1;
    }
    r
}

fn static_checks() {
    let x = count_up_to(5);
    let v = vec![2,3];
    assert(x@.map_values(|x| x as nat) == v@.map_values(|x| x as nat)) by {
        reveal_with_fuel(primes_bellow, 4);
        assert(!is_prime(0));
        assert(!is_prime(1));
        assert(is_prime(2));
        assert(is_prime(3)) by {
            assert(tdiv(3, 2) != 0);
        }
        assert(!is_prime(4)) by {
            assert(tdiv(4, 2) == 0);
        }
    };
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def count_up_to(n):
    """Implement a function that takes an non-negative integer and returns an array of the first n
    integers that are prime numbers and less than n.
    for example:
    count_up_to(5) => [2,3]
    count_up_to(11) => [2,3,5,7]
    count_up_to(0) => []
    count_up_to(20) => [2,3,5,7,11,13,17,19]
    count_up_to(1) => []
    count_up_to(18) => [2,3,5,7,11,13,17]
    """

*/

/*
### ENTRY POINT
count_up_to
*/

/*
### CANONICAL SOLUTION
    primes = []
    for i in range(2, n):
        is_prime = True
        for j in range(2, i):
            if i % j == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(i)
    return primes


*/

/*
### TEST
def check(candidate):

    assert candidate(5) == [2,3]
    assert candidate(6) == [2,3,5]
    assert candidate(7) == [2,3,5]
    assert candidate(10) == [2,3,5,7]
    assert candidate(0) == []
    assert candidate(22) == [2,3,5,7,11,13,17,19]
    assert candidate(1) == []
    assert candidate(18) == [2,3,5,7,11,13,17]
    assert candidate(47) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    assert candidate(101) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


*/

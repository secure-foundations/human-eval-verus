/*
### ID
HumanEval/75
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> bool {
    p > 1 &&
    forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}

fn prime(p: u64) -> (ret: bool)
    ensures
        ret <==> spec_prime(p as int),
{
    for k in 2..p {
        if p % k == 0 {
            return false;
        }
    }
    true
}

fn is_multiply_prime(x: u64) -> (ans: bool)
    requires x > 1,
    ensures ans <==> exists|a: int, b: int, c: int| 
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
{
    for a in 2..x+1
        invariant forall|i: int, j: int, k: int| 
            (spec_prime(i) && spec_prime(j) && spec_prime(k) && i < a as int) ==> x != i * j * k,
    {
        if prime(a) {
            for b in 2..x+1
                invariant forall|j: int, k: int| 
                    (spec_prime(j) && spec_prime(k) && j < b as int) ==> x != (a as int) * j * k,
            {
                if prime(b) {
                    for c in 2..x+1
                        invariant forall|k: int| 
                            (spec_prime(k) && k < c as int) ==> x != (a as int) * (b as int) * k,
                    {
                        if prime(c) && x == a * b * c {
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def is_multiply_prime(a):
    """Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise.
    Knowing that (a) is less then 100.
    Example:
    is_multiply_prime(30) == True
    30 = 2 * 3 * 5
    """

*/

/*
### ENTRY POINT
is_multiply_prime
*/

/*
### CANONICAL SOLUTION
    def is_prime(n):
        for j in range(2,n):
            if n%j == 0:
                return False
        return True

    for i in range(2,101):
        if not is_prime(i): continue
        for j in range(2,101):
            if not is_prime(j): continue
            for k in range(2,101):
                if not is_prime(k): continue
                if i*j*k == a: return True
    return False

*/

/*
### TEST
def check(candidate):

    assert candidate(5) == False
    assert candidate(30) == True
    assert candidate(8) == True
    assert candidate(10) == False
    assert candidate(125) == True
    assert candidate(3 * 5 * 7) == True
    assert candidate(3 * 6 * 7) == False
    assert candidate(9 * 9 * 9) == False
    assert candidate(11 * 9 * 9) == False
    assert candidate(11 * 13 * 7) == True


*/

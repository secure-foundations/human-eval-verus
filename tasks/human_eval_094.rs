/*
### ID
HumanEval/94
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

pub open spec fn is_prime_spec(n: nat) -> bool {
    (n > 1) && forall|i| 1 < i < n ==> #[trigger] (n % i) != 0
}

pub closed spec fn is_prime_so_far(n: nat, k: nat) -> bool
    recommends
        n >= k > 1,
{
    forall|i| 1 < i < k ==> #[trigger] (n % i) != 0
}

fn is_prime(n: u32) -> (res: bool)
    ensures
        res == is_prime_spec(n as nat),
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
        decreases n - k,
    {
        assert((is_prime_so_far(n as nat, k as nat) && (n as nat) % (k as nat) != 0)
            == is_prime_so_far(n as nat, (k + 1) as nat));

        res = res && n % k != 0;
        k = k + 1;
    }
    return res;
}

pub open spec fn spec_sum_digits(n: nat) -> nat
    decreases n,
{
    if n < 10 {
        n
    } else {
        (n % 10) + spec_sum_digits(n / 10)
    }
}

pub proof fn sum_digits_decreases(x: nat)
    requires
        x >= 10,
    ensures
        spec_sum_digits(x) <= x,
    decreases x,
{
    let sub_x = x / 10;
    let inc_x = x % 10;

    if sub_x >= 10 {
        sum_digits_decreases(sub_x);
        assert(inc_x + sub_x <= x + 10);
    } else {
        assert(inc_x + spec_sum_digits(sub_x) <= sub_x + 10);
    }
}

fn sum_digits(n: u32) -> (count: u32)
    ensures
        count == spec_sum_digits(n as nat),
    decreases n,
{
    if n < 10 {
        n
    } else {
        assert(spec_sum_digits((n as nat)) <= n) by { sum_digits_decreases(n as nat) };
        (n % 10) + sum_digits(n / 10)
    }
}

pub open spec fn spec_find_largest_prime_so_far(s: Seq<nat>, i: nat) -> nat
    recommends
        0 <= i <= s.len(),
    decreases i,
{
    if i <= 0 {
        0
    } else {
        let first_i = s.take(i as int);  // first i numbers

        // largest of the first i-i numbers in the list
        let largest_in_front = spec_find_largest_prime_so_far(s, (i - 1) as nat);

        // is the i'th number prime and bigger than the largest of the first i-1 numbers?
        if is_prime_spec(first_i.last()) && first_i.last() > largest_in_front {
            first_i.last()
        } else {
            largest_in_front
        }
    }
}

pub open spec fn spec_find_largest_prime(s: Seq<nat>) -> nat {
    spec_find_largest_prime_so_far(s, s.len())
}

fn find_largest_prime(lst: Vec<u32>) -> (ret: u32)
    ensures
        ret == spec_find_largest_prime(lst@.map_values(|val: u32| val as nat)),
{
    let mut largest_prime = 0;
    for i in 0..lst.len()
        invariant
            largest_prime == 0 || is_prime_spec(largest_prime as nat),
            largest_prime == spec_find_largest_prime_so_far(
                lst@.map_values(|val: u32| val as nat),
                i as nat,
            ),
    {
        let num = lst[i];
        if is_prime(num) && num > largest_prime {
            largest_prime = num;
        }
    }
    largest_prime
}

// note: "skjkasdkd" is the specified function name
fn skjkasdkd(lst: Vec<u32>) -> (ret: u32)
    ensures
        ret == spec_sum_digits(
            spec_find_largest_prime(lst@.map_values(|val: u32| val as nat)) as nat,
        ),
{
    let largest_prime = find_largest_prime(lst);
    let total = sum_digits(largest_prime);
    total
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def skjkasdkd(lst):
    """You are given a list of integers.
    You need to find the largest prime value and return the sum of its digits.

    Examples:
    For lst = [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] the output should be 10
    For lst = [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] the output should be 25
    For lst = [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] the output should be 13
    For lst = [0,724,32,71,99,32,6,0,5,91,83,0,5,6] the output should be 11
    For lst = [0,81,12,3,1,21] the output should be 3
    For lst = [0,8,1,2,1,7] the output should be 7
    """

*/

/*
### ENTRY POINT
skjkasdkd
*/

/*
### CANONICAL SOLUTION
def skjkasdkd(lst):
    def isPrime(n):
        for i in range(2,int(n**0.5)+1):
            if n%i==0:
                return False

        return True
    maxx = 0
    i = 0
    while i < len(lst):
        if(lst[i] > maxx and isPrime(lst[i])):
            maxx = lst[i]
        i+=1
    result = sum(int(digit) for digit in str(maxx))
    return result


*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3]) == 10, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1]) == 25, "This prints if this assert fails 2 (also good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3]) == 13, "This prints if this assert fails 3 (also good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([0,724,32,71,99,32,6,0,5,91,83,0,5,6]) == 11, "This prints if this assert fails 4 (also good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([0,81,12,3,1,21]) == 3, "This prints if this assert fails 5 (also good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([0,8,1,2,1,7]) == 7, "This prints if this assert fails 6 (also good for debugging!)"

    assert candidate([8191]) == 19, "This prints if this assert fails 7 (also good for debugging!)"
    assert candidate([8191, 123456, 127, 7]) == 19, "This prints if this assert fails 8 (also good for debugging!)"
    assert candidate([127, 97, 8192]) == 10, "This prints if this assert fails 9 (also good for debugging!)"

*/

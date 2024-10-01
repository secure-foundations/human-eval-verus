/*
### ID
HumanEval/139
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::arithmetic::mul::*;

verus! {

    // specification

    pub closed spec fn brazilian_factorial_helper(start : int, end : int, fact_i : int, special_fact : int) -> int
        decreases (end - start)
    {
        if (end - start <= 0) {
            special_fact
        } else {
            brazilian_factorial_helper(start + 1, end, fact_i * start, special_fact * (fact_i * start))
        }
    }

    pub closed spec fn brazilian_factorial(n : int) -> int 
    {
        brazilian_factorial_helper(1int, n + 1, 1, 1)
    }


    // implementation
    proof fn lemma_bf_helper_is_increasing(start : nat, end : nat, fact_i : nat, special_fact : nat)
        requires 
            start >= 1, 
            fact_i >= 1,
            special_fact >= 1,
        ensures
            special_fact <= brazilian_factorial_helper(start as int, end as int, fact_i as int, special_fact as int)
        decreases (end - start)
    {
        if (end - start <= 0) {
        } else {
            assert (fact_i * start >= 1) by {lemma_mul_strictly_positive(fact_i as int, start as int)};
            assert ((special_fact * (fact_i * start)) >= special_fact) by {lemma_mul_ordering(special_fact as int, (fact_i * start) as int)};            
            assert (brazilian_factorial_helper((start + 1) as int, end as int, (fact_i * start) as int, (special_fact * (fact_i * start)) as int) >=
                    (special_fact * (fact_i * start)))
                    by {lemma_bf_helper_is_increasing(start + 1, end, fact_i * start, special_fact * (fact_i * start))};
        }
    }

    pub fn brazilian_factorial_impl(n : u32) -> (bf : u32)
        requires 
            0 < n < 4294967295,
            (brazilian_factorial(n as int) <= 4294967295)
        ensures brazilian_factorial(n as int) == bf
    {
        let mut start = 1u32;
        let mut end = n + 1u32;
        let mut fact_i = 1u32;
        let mut special_fact = 1u32;

        assert (special_fact <= brazilian_factorial_helper(1, n+1, 1, 1)) by {lemma_bf_helper_is_increasing(1, (n+1) as nat, 1, 1)};

        while start < end 
            invariant 
                brazilian_factorial_helper(start as int, end as int, fact_i as int, special_fact as int) == brazilian_factorial_helper(1, n+1, 1, 1),
                special_fact <= brazilian_factorial_helper(1, n+1, 1, 1),
                start >= 1,
                fact_i >= 1,
                special_fact >= 1,
                (brazilian_factorial_helper(1, n+1, 1, 1) <= 4294967295)
            decreases (end - start),

        {
            assert (special_fact <= brazilian_factorial_helper(start as int, end as int, fact_i as int, special_fact as int)) by {lemma_bf_helper_is_increasing(start as nat, end as nat, fact_i as nat, special_fact as nat)};
            
            assert ((fact_i * start) as int >= 1) by {lemma_mul_strictly_positive(fact_i as int, start as int)};
            assert ((special_fact * (fact_i * start) as int) as int >= special_fact) by {lemma_mul_ordering(special_fact as int, (fact_i * start) as int)};
            assert (((special_fact * fact_i) as int * start) as int >= special_fact) by {lemma_mul_is_associative(special_fact as int, fact_i as int, start as int)};
            
            assert ((special_fact * (fact_i * start) as int) as int  <= 
                      brazilian_factorial_helper(start + 1 as int, end as int, (fact_i * start) as int, special_fact * (fact_i * start) as int) as int) by {lemma_bf_helper_is_increasing((start + 1) as nat, end as nat, (fact_i * start) as nat, (special_fact * (fact_i * start)) as nat)};

            assert ((fact_i * start) as int <= (special_fact * (fact_i * start) as int) as int) by {lemma_mul_ordering(special_fact as int, (fact_i * start) as int)};

            fact_i = fact_i * start;
            special_fact = special_fact * fact_i;
            start = start + 1;
        }
        

        return special_fact;
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


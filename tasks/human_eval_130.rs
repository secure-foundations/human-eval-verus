/*
### ID
HumanEval/130
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_tri(n: nat) -> nat
    decreases
            if n % 2 == 0 {
                0
            } else {
                n
            },
{
    if n == 1 {
        3
    } else if n % 2 == 0 {
        1 + n / 2
    } else {
        spec_tri((n - 1) as nat) + spec_tri((n - 2) as nat) + spec_tri(n + 1)
    }
}

fn checked_add_three(a: Option<u32>, b: Option<u32>, c: Option<u32>) -> (r: Option<u32>)
    ensures
        r.is_some() && a.is_some() && b.is_some() && c.is_some() ==> r.unwrap() == a.unwrap()
            + b.unwrap() + c.unwrap(),
        a.is_none() || b.is_none() || c.is_none() ==> r.is_none(),
        !(a.is_none() || b.is_none() || c.is_none()) && r.is_none() ==> a.unwrap() + b.unwrap()
            + c.unwrap() > u32::MAX,
{
    a?.checked_add(b?)?.checked_add(c?)
}

#[verifier::loop_isolation(false)]
fn tri(n: u32) -> (result: Vec<Option<u32>>)
    requires
        n + 1 <= u32::MAX,
    ensures
        result.len() == n + 1,
        forall|i: int|
            #![trigger result[i]]
            0 <= i < result.len() ==> {
                (result[i].is_some() ==> result[i].unwrap() == spec_tri(i as nat)) && (
                result[i].is_none() ==> spec_tri(i as nat) > u32::MAX)
            },
{
    if n == 0 {
        vec![Some(1)]
    } else {
        let mut result: Vec<Option<u32>> = vec![Some(1), Some(3)];
        let mut i = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                result.len() == i,
                forall|j: int|
                    #![trigger result[j]]
                    0 <= j < i ==> ((result[j].is_some() ==> result[j].unwrap() == spec_tri(
                        j as nat,
                    )) && (result[j].is_none() ==> spec_tri(j as nat) > u32::MAX)),
        {
            if i % 2 == 0 {
                result.push(Some(1 + (i / 2)));
                assert(result[i as int].unwrap() == spec_tri(i as nat));
            } else {
                assert((i + 1) / 2 + 1 == (i + 3) / 2);
                let cur = checked_add_three(
                    result[i as usize - 2],
                    result[i as usize - 1],
                    Some((i + 1) / 2 + 1),
                );
                proof {
                    if result[i - 2].is_some() && result[i - 1].is_some() {
                        assert(result[i - 2].unwrap() == spec_tri((i - 2) as nat));
                        assert(result[i - 1].unwrap() == spec_tri((i - 1) as nat));
                        assert((i + 3) / 2 == spec_tri((i + 1) as nat));
                    } else {
                        assert(cur.is_none());
                    }
                    assert(cur.is_some() ==> cur.unwrap() == spec_tri(i as nat));
                }
                result.push(cur);
                assert(result[i as int].is_some() ==> result[i as int].unwrap() == spec_tri(
                    i as nat,
                ));
            }
            i += 1;
        }
        assert(result.len() == n + 1);
        result
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def tri(n):
    """Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
    the last couple centuries. However, what people don't know is Tribonacci sequence.
    Tribonacci sequence is defined by the recurrence:
    tri(1) = 3
    tri(n) = 1 + n / 2, if n is even.
    tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
    For example:
    tri(2) = 1 + (2 / 2) = 2
    tri(4) = 3
    tri(3) = tri(2) + tri(1) + tri(4)
           = 2 + 3 + 3 = 8
    You are given a non-negative integer number n, you have to a return a list of the
    first n + 1 numbers of the Tribonacci sequence.
    Examples:
    tri(3) = [1, 3, 2, 8]
    """

*/

/*
### ENTRY POINT
tri
*/

/*
### CANONICAL SOLUTION
    if n == 0:
        return [1]
    my_tri = [1, 3]
    for i in range(2, n + 1):
        if i % 2 == 0:
            my_tri.append(i / 2 + 1)
        else:
            my_tri.append(my_tri[i - 1] + my_tri[i - 2] + (i + 3) / 2)
    return my_tri

*/

/*
### TEST
def check(candidate):

    # Check some simple cases

    assert candidate(3) == [1, 3, 2.0, 8.0]
    assert candidate(4) == [1, 3, 2.0, 8.0, 3.0]
    assert candidate(5) == [1, 3, 2.0, 8.0, 3.0, 15.0]
    assert candidate(6) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0]
    assert candidate(7) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0]
    assert candidate(8) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0]
    assert candidate(9) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0, 35.0]
    assert candidate(20) == [1, 3, 2.0, 8.0, 3.0, 15.0, 4.0, 24.0, 5.0, 35.0, 6.0, 48.0, 7.0, 63.0, 8.0, 80.0, 9.0, 99.0, 10.0, 120.0, 11.0]

    # Check some edge cases that are easy to work out by hand.
    assert candidate(0) == [1]
    assert candidate(1) == [1, 3]

*/

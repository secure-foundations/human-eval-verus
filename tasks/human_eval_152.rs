/*
### ID
HumanEval/152
*/
/*
### VERUS BEGIN
*/
use vstd::math::abs as vabs;
use vstd::prelude::*;

verus! {

fn abs(x: i64) -> (r: i64)
    requires
        x != i64::MIN,
    ensures
        r == vabs(x as int),
{
    if x < 0 {
        -x
    } else {
        x
    }
}

#[verifier::loop_isolation(false)]
fn compare(scores: &[i32], guesses: &[i32]) -> (result: Vec<i64>)
    requires
        scores.len() == guesses.len(),
    ensures
        result.len() == scores.len(),
        forall|i: int| #![auto] 0 <= i < result.len() ==> result[i] == vabs(scores[i] - guesses[i]),
{
    let mut result = Vec::with_capacity(scores.len());
    let mut i = 0;
    for i in 0..scores.len()
        invariant
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == vabs(scores[j] - guesses[j]),
    {
        result.push(abs(scores[i] as i64 - guesses[i] as i64));
    }
    result
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def compare(game,guess):
    """I think we all remember that feeling when the result of some long-awaited
    event is finally known. The feelings and thoughts you have at that moment are
    definitely worth noting down and comparing.
    Your task is to determine if a person correctly guessed the results of a number of matches.
    You are given two arrays of scores and guesses of equal length, where each index shows a match.
    Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
    the value is 0, and if not, the value is the absolute difference between the guess and the score.


    example:

    compare([1,2,3,4,5,1],[1,2,3,4,2,-2]) -> [0,0,0,0,3,3]
    compare([0,5,0,0,0,4],[4,1,1,0,0,-2]) -> [4,4,1,0,0,6]
    """

*/

/*
### ENTRY POINT
compare
*/

/*
### CANONICAL SOLUTION
    return [abs(x-y) for x,y in zip(game,guess)]

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1,2,3,4,5,1],[1,2,3,4,2,-2])==[0,0,0,0,3,3], "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([0,0,0,0,0,0],[0,0,0,0,0,0])==[0,0,0,0,0,0], "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1,2,3],[-1,-2,-3])==[2,4,6], "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([1,2,3,5],[-1,2,3,4])==[2,0,0,1], "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"


*/

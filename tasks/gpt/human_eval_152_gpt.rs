/// I think we all remember that feeling when the result of some long-awaited
/// event is finally known. The feelings and thoughts you have at that moment are
/// definitely worth noting down and comparing.
/// Your task is to determine if a person correctly guessed the results of a number of matches.
/// You are given two arrays of scores and guesses of equal length, where each index shows a match. 
/// Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
/// the value is 0, and if not, the value is the absolute difference between the guess and the score.
///
/// # Examples
///
/// ```
/// compare(&[1,2,3,4,5,1], &[1,2,3,4,2,-2]) -> Vec<i32> // should return [0,0,0,0,3,3]
/// compare(&[0,5,0,0,0,4], &[4,1,1,0,0,-2]) -> Vec<i32> // should return [4,4,1,0,0,6]
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn compare(game: Vec<i32>, guess: Vec<i32>) -> (result: Vec<i32>)
{
    let mut differences: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < game.len() {
        let diff = if game[i] > guess[i] { game[i] - guess[i] } else { guess[i] - game[i] };
        differences.push(diff);
        i += 1;
    }
    differences
}
}

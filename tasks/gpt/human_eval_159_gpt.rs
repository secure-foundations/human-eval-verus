/// You're a hungry rabbit, and you already have eaten a certain number of carrots,
/// but now you need to eat more carrots to complete the day's meals.
/// you should return a tuple of (total number of eaten carrots after your meals,
/// the number of carrots left after your meals)
/// if there are not enough remaining carrots, you will eat all remaining carrots, but will still be hungry.
///
/// Example:
/// * eat(5, 6, 10) -> (11, 4)
/// * eat(4, 8, 9) -> (12, 1)
/// * eat(1, 10, 10) -> (11, 0)
/// * eat(2, 11, 5) -> (7, 0)
///
/// Variables:
/// @number: u32
///     the number of carrots that you have eaten.
/// @need: u32
///     the number of carrots that you need to eat.
/// @remaining: u32
///     the number of remaining carrots that exist in stock
///
/// Constraint:
/// * 0 <= number <= 1000
/// * 0 <= need <= 1000
/// * 0 <= remaining <= 1000
///
/// Have fun :)

use vstd::prelude::*;
fn main() {}

verus!{

pub struct EatResult {
    new_number: u32,
    new_remaining: u32,
}

fn eat(number: u32, need: u32, remaining: u32) -> EatResult {
    
    let eatable = if remaining < need { remaining } else { need };
    let new_number = number + eatable;
    let new_remaining = if remaining >= need { remaining - need } else { 0 };
    
    EatResult { new_number, new_remaining }
}
}

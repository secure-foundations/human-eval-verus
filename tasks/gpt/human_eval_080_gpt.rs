/// You are given a string s.
/// Your task is to check if the string is happy or not.
/// A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
/// For example:
/// is_happy("a") => false
/// is_happy("aa") => false
/// is_happy("abcd") => true
/// is_happy("aabb") => false
/// is_happy("adb") => true
/// is_happy("xyy") => false

use vstd::prelude::*;
fn main() {
    let my_string = "example";
    let char_vec: Vec<char> = my_string.chars().collect();
    let result = is_happy(&char_vec);
    println!("Is the string happy? {}", result);
}

verus!{
fn is_happy(chars: &Vec<char>) -> (result: bool) {
    if chars.len() < 3 {
        return false;
    }
    
    let mut i = 0;
    while i < chars.len() - 2 {
        if chars[i] == chars[i + 1] || chars[i] == chars[i + 2] || chars[i + 1] == chars[i + 2] {
            return false;
        }
        i += 1;
    }
    true
}
}

/// You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word
/// cycpattern_check("abcd","abd") => False
/// cycpattern_check("hello","ell") => True
/// cycpattern_check("whassup","psus") => False
/// cycpattern_check("abab","baa") => True
/// cycpattern_check("efef","eeff") => False
/// cycpattern_check("himenss","simen") => True

use vstd::prelude::*;
fn main() {}

verus!{
fn cycpattern_check(a: Vec<char>, b: Vec<char>) -> (result: bool) {
    let mut bb = b.clone();
    let mut i = 0;
    while i < b.len() {
        if contains(&a, &bb) {
            return true;
        }
        let ch = bb.remove(0);
        bb.push(ch);
        i += 1;
    }
    false
}

fn contains(a: &Vec<char>, b: &Vec<char>) -> bool {
    if b.len() > a.len() {
        return false;
    }
    let mut start = 0;
    while start <= a.len() - b.len() {
        let mut matches = true;
        for i in 0..b.len() {
            if a[start + i] != b[i] {
                matches = false;
                break;
            }
        }
        if matches {
            return true;
        }
        start += 1;
    }
    false
}
}

/// Given a string representing a space separated lowercase letters, return a dictionary
/// of the letter with the most repetition and containing the corresponding count.
/// If several letters have the same occurrence, return all of them.
///
/// Example:
/// histogram("a b c") == {'a': 1, 'b': 1, 'c': 1}
/// histogram("a b b a") == {'a': 2, 'b': 2}
/// histogram("a b c a b") == {'a': 2, 'b': 2}
/// histogram("b b b b a") == {'b': 4}
/// histogram("") == {}
///
/// Note: In Rust, we use `HashMap` instead of `dictionary`.

use std::collections::HashMap;

fn histogram(text: &str) -> HashMap<char, i32> {
    let mut counts = HashMap::new();
    let mut max_count = 0;

    for c in text.chars() {
        if !c.is_whitespace() {
            let count = counts.entry(c).or_insert(0);
            *count += 1;
            if *count > max_count {
                max_count = *count;
            }
        }
    }

    counts.retain(|_, v| *v == max_count);
    counts
}

fn main() {
    // Example usage:
    let text = "example text with some words";
    let hist = histogram(text);
    println!("{:?}", hist);
}

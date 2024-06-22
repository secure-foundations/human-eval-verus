/// You'll be given a string of words, and your task is to count the number
/// of boredoms. A boredom is a sentence that starts with the word "I".
/// Sentences are delimited by '.', '?' or '!'.
///
/// For example:
/// ```
/// assert_eq!(is_bored("Hello world"), 0);
/// assert_eq!(is_bored("The sky is blue. The sun is shining. I love this weather"), 1);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn is_bored(S: &Vec<char>) -> (ret: usize) {
    let mut count = 0;
    let mut sentence_start = true;
    let mut i_is_first = false;
    let mut index = 0;

    while index < S.len() {
        let c = S[index];
        match c {
            '.' | '?' | '!' => {
                if i_is_first {
                    count += 1;
                }
                sentence_start = true;
                i_is_first = false;
            }
            ' ' => {
                if sentence_start {
                    sentence_start = false;
                }
            }
            'I' if sentence_start => {
                i_is_first = true;
                sentence_start = false;
            }
            _ => {
                if sentence_start {
                    sentence_start = false;
                }
                if i_is_first {
                    i_is_first = false;
                }
            }
        }
        index += 1;
    }

    // Check for the last sentence if it ends without punctuation
    if i_is_first {
        count += 1;
    }

    count
}
}

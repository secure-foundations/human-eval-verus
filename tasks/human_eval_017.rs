/*
### ID
HumanEval/17
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// TODO: Put your solution (the specification, implementation, and proof) to the task here

pub open spec fn spec_parse_music(s: Seq<char>) -> Option<Seq<int>>
    decreases s.len()
{
    if s.len() == 0 {
        Some(seq![])
    } else if s.len() >= 2 && s[0] == 'o' && s[1] == '|' {
        if let Some(rest) = spec_parse_music(s.skip(2)) {
            Some(seq![2] + rest)
        } else { None }
    } else if s.len() >= 2 && s[0] == '.' && s[1] == '|' {
        if let Some(rest) = spec_parse_music(s.skip(2)) {
            Some(seq![1] + rest)
        } else { None }
    } else if s.len() != 0 && s[0] == 'o' {
        if let Some(rest) = spec_parse_music(s.skip(1)) {
            Some(seq![4] + rest)
        } else { None }
    } else if s.len() != 0 && s[0] == ' ' {
        // Somewhat more lenient: allows multiple spaces between notes
        spec_parse_music(s.drop_first())
    } else {
        None
    }
}

pub fn parse_music(s: &str) -> (res: Option<Vec<u8>>)
    ensures
        res matches Some(res) ==> spec_parse_music(s@) == Some(res@.map_values(|b| b as int)),
        res is None ==> spec_parse_music(s@) is None,
{
    let s_len = s.unicode_len();
    let mut beats = vec![];
    let mut i = 0;

    assert(s@.skip(0) == s@);

    while i < s_len
        invariant
            s_len == s@.len(),
            0 <= i <= s_len,
            spec_parse_music(s@) matches Some(all_beats) ==> {
                &&& spec_parse_music(s@.skip(i as int)) matches Some(rest)
                &&& all_beats =~= beats@.map_values(|b| b as int) + rest
            },
            spec_parse_music(s@.skip(i as int)) matches Some(rest)
                ==> spec_parse_music(s@) matches Some(all_beats),
            spec_parse_music(s@.skip(i as int)) is None ==>
                spec_parse_music(s@) is None,

        decreases s_len - i,
    {
        let c = s.get_char(i);

        assert(s@.skip(i as int).skip(1) == s@.skip(i + 1));
        assert(s@.len() >= i + 2 ==> s@.skip(i as int).skip(2) == s@.skip(i + 2));

        if c == ' ' {
            i += 1;
            continue;
        }

        if i < s_len - 1 {
            let c2 = s.get_char(i + 1);

            if c == 'o' && c2 == '|' {
                beats.push(2);
                i += 2;
                continue;
            } else if c == '.' && c2 == '|' {
                beats.push(1);
                i += 2;
                continue;
            }
        }

        if c == 'o' {
            beats.push(4);
            i += 1;
        } else {
            return None;
        }
    }

    Some(beats)
}

} // verus!
fn main() {
    // eprintln!("{:?}", parse_music("o o| .| o| o| .| .| .| .| o o"));
}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def parse_music(music_string: str) -> List[int]:
    """ Input to this function is a string representing musical notes in a special ASCII format.
    Your task is to parse this string and return list of integers corresponding to how many beats does each
    not last.

    Here is a legend:
    'o' - whole note, lasts four beats
    'o|' - half note, lasts two beats
    '.|' - quater note, lasts one beat

    >>> parse_music('o o| .| o| o| .| .| .| .| o o')
    [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
    """

*/

/*
### ENTRY POINT
parse_music
*/

/*
### CANONICAL SOLUTION
    note_map = {'o': 4, 'o|': 2, '.|': 1}
    return [note_map[x] for x in music_string.split(' ') if x]

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == []
    assert candidate('o o o o') == [4, 4, 4, 4]
    assert candidate('.| .| .| .|') == [1, 1, 1, 1]
    assert candidate('o| o| .| .| o o o o') == [2, 2, 1, 1, 4, 4, 4, 4]
    assert candidate('o| .| o| .| o o| o o|') == [2, 1, 2, 1, 4, 2, 4, 2]

*/

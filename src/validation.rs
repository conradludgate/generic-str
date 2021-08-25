use crate::string_base::StringBase;

// truncate `&StringBase<[u8]>` to length at most equal to `max`
// return `true` if it were truncated, and the new str.
pub(super) fn truncate_to_char_boundary(
    s: &StringBase<[u8]>,
    mut max: usize,
) -> (bool, &StringBase<[u8]>) {
    if max >= s.len() {
        (false, s)
    } else {
        while !s.is_char_boundary(max) {
            max -= 1;
        }
        (true, &s[..max])
    }
}

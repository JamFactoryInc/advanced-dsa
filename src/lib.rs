#![feature(btree_cursors)]
#![feature(new_range_api)]
#![feature(allocator_api)]
extern crate core;

mod reservation_map;

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}

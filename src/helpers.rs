

pub fn get_bits(hi: u32, lo: u32, word: u32) -> u32 {
   (word >> lo) & (2_u32.pow(1+hi-lo)-1)
}

pub fn splice_bits(hi: u32, lo: u32, dest: u32, source: u32) -> u32 {
    let mask = 2_u32.pow(1 + hi - lo) - 1;
    ((source & mask) << lo) | (dest & !(mask << lo))
}

pub fn twos_complement(word: u32, num_bits: u32) -> i32 {
    let mut result = word;
    let ones: u32 = ((2_u64.pow(32)-1) as u32) - (2_u32.pow(num_bits)-1);
    if word & 2_u32.pow(num_bits-1) != 0 {
        result |= ones; 
    }
    result as i32
}

#[cfg(test)]
mod helper_tests {
    use super::*;

    #[test]
    fn test_get_bits() {
        let test_bits = 0b0101_0000_1010_1111;
        assert_eq!(0b0101, get_bits(15, 12, test_bits));
        assert_eq!(0b0000, get_bits(11, 8, test_bits));
        assert_eq!(0b1010, get_bits(7, 4, test_bits));
        assert_eq!(0b1111, get_bits(3, 0, test_bits));
        assert_eq!(0b1, get_bits(14, 14, test_bits));
        assert_eq!(0b0, get_bits(11, 11, test_bits));
    }

    #[test]
    fn test_splice_bits() {
        let test_bits = 0b0000_1010_1111_1110;
        assert_eq!(0b0101_1010_1111_1110, splice_bits(15, 12, test_bits, 0b0101));
        assert_eq!(0b0000_1111_1111_1110, splice_bits(11, 8, test_bits, 0b1111));
        assert_eq!(0b0000_1010_0000_1110, splice_bits(7, 4, test_bits, 0b0000));
        assert_eq!(0b0000_1010_1111_0001, splice_bits(3, 0, test_bits, 0b0001));
        assert_eq!(0b0000_0000_0000_1110, splice_bits(11, 4, test_bits, 0b0000_0000));
        assert_eq!(0b1111_1111_1111_1110, splice_bits(15, 8, test_bits, 0b1111_1111));
        assert_eq!(0b1000_1010_1111_1110, splice_bits(15, 15, test_bits, 0b1));
    }

    #[test]
    fn twos_complement_test() {
        let positive_test_bits = 0b0101;
        let negative_test_bits = 0b1011;
        assert_eq!(0b0101, twos_complement(positive_test_bits, 4));
        assert_eq!(-5, twos_complement(negative_test_bits, 4));
    }
}

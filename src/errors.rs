/// Error types.

use bitcoin::FeeRate;
use bitcoin::Weight;
use std::{error::Error, fmt};

#[derive(Debug)]
pub enum LibError {
    Multiplication(Weight, FeeRate),
}

#[cfg(any(test, feature = "rand"))]
impl Error for LibError {}

#[cfg(any(test, feature = "rand"))]
impl fmt::Display for LibError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LibError::Multiplication(weight, fee_rate) => {
                write!(f, "{} * {} exceeds u64 Max", weight, fee_rate)
            }
        }
    }
}

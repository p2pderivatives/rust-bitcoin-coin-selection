/// Error types.
use bitcoin::FeeRate;
use bitcoin::Weight;
use std::error::Error as E;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    MultiplicationOverflow(Weight, FeeRate),
    AdditionOverflow(Weight, Weight),
}

impl E for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::MultiplicationOverflow(one, two) => {
                write!(f, "{} * {} exceeds u64 Max", one, two)
            }
            Error::AdditionOverflow(one, two) => {
                write!(f, "{} + {} exceeds u64 Max", one, two)
            }
        }
    }
}

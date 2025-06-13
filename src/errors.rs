/// Error types.
use std::error::Error as E;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum OverflowError {
    Addition,
    Multiplication,
    Subtraction,
}

impl E for OverflowError {}

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            OverflowError::Addition => {
                write!(f, "Arithmetic overflow during addition")
            }
            OverflowError::Multiplication => {
                write!(f, "Arithmetic overflow during multiplication")
            }
            OverflowError::Subtraction => {
                write!(f, "Arithmetic overflow during subtraction")
            }
        }
    }
}

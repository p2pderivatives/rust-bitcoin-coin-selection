/// Error types.

#[derive(Clone, Debug, PartialEq)]
pub enum SelectionError {
    InsufficentFunds,
    IterationLimitReached,
    MaxWeightExceeded,
    Overflow(OverflowError),
    ProgramError,
    SolutionNotFound,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverflowError {
    Addition,
    Multiplication,
    Subtraction,
}

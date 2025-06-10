/// Error types.

#[derive(Clone, Debug, PartialEq)]
pub enum SelectionError {
    Overflow(OverflowError),
    InsufficentFunds,
    SolutionNotFound,
    IterationLimitReached,
    ProgramError,
}

#[derive(Clone, Debug, PartialEq)]
pub enum OverflowError {
    Addition,
    Multiplication,
    Subtraction,
}

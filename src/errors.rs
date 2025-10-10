#[derive(Clone, Debug, PartialEq)]
/// Error types returned during the selection process when no match is found.
pub enum SelectionError {
    /// The sum of values passed is less than the target.  That is, There is no possible solution.
    InsufficentFunds,
    /// The maximum iteration count was reached returning no result.  That is, A solution
    /// may exist but could not be found in a reasonable time.
    IterationLimitReached,
    /// The weight of a selection exceeded the max weight limit returning no result.
    /// That is, No solutions could be found that are less than the `max_weight` parameter.
    MaxWeightExceeded,
    /// A numeric overflow occurred and the selection process aborted returning no result.
    Overflow(OverflowError),
    /// A generic error that should not happen assuming code paths behave as known.
    ProgramError,
    /// Search space was exhausted without yielding a result.  That is, iteration limit was not hit
    /// and yet no solution could be found.
    SolutionNotFound,
}

#[derive(Clone, Debug, PartialEq)]
/// The possible numeric overflows that may occur.
pub enum OverflowError {
    /// Bounds overflowed while performing addition.
    Addition,
    /// Bounds overflowed wile performing multiplication.
    Multiplication,
    /// Bounds overflowed while performing subtraction.
    Subtraction,
}

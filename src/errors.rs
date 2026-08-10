//! Possible error types if no match is found.

use crate::ITERATION_LIMIT;
use bitcoin_units::{Amount, Weight};

use crate::weighted_utxo::WeightedUtxo;

/// Error types returned during the selection process when no match is found.
#[derive(Clone, Debug, PartialEq)]
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

impl SelectionError {
    pub(crate) fn pre_handler(
        target: Amount,
        weighted_utxos: &[WeightedUtxo],
    ) -> Result<(u64, Weight), Self> {
        let (amount_sum, weight_sum) = weighted_utxos
            .iter()
            .map(|u| (u.effective_value, u.weight))
            .try_fold((0u64, Weight::ZERO), |acc, u| {
                let amount = acc.0.checked_add(u.0);
                let weight = acc.1.checked_add(u.1);

                if amount.is_none() || weight.is_none() {
                    None
                } else if amount.is_some() && amount.unwrap() > Amount::MAX.to_sat() {
                    None
                } else {
                    Some((amount.unwrap(), weight.unwrap()))
                }
            })
            .ok_or(Self::Overflow(OverflowError::Addition))?;

        if weighted_utxos.is_empty() {
            Err(Self::SolutionNotFound)
        } else if amount_sum < target.to_sat() {
            Err(Self::InsufficentFunds)
        } else {
            Ok((amount_sum, weight_sum))
        }
    }

    pub(crate) fn handler<T>(
        result: Vec<&T>,
        iterations: u32,
        weight_exceeded: bool,
    ) -> crate::Return<'_, T> {
        if result.is_empty() && iterations == ITERATION_LIMIT {
            Err(Self::IterationLimitReached)
        } else if result.is_empty() && weight_exceeded {
            Err(Self::MaxWeightExceeded)
        } else if result.is_empty() {
            Err(Self::SolutionNotFound)
        } else {
            Ok((iterations, result))
        }
    }

    pub(crate) fn srd_handler<T>(
        result: Vec<&T>,
        iterations: u32,
        weight_exceeded: bool,
    ) -> crate::Return<'_, T> {
        if result.is_empty() && weight_exceeded {
            Err(Self::MaxWeightExceeded)
        } else if result.is_empty() {
            Err(Self::SolutionNotFound)
        } else {
            Ok((iterations, result))
        }
    }
}

/// The possible numeric overflows that may occur.
#[derive(Clone, Debug, PartialEq)]
pub enum OverflowError {
    /// Bounds overflowed while performing addition.
    Addition,
    /// Bounds overflowed wile performing multiplication.
    Multiplication,
    /// Bounds overflowed while performing subtraction.
    Subtraction,
}

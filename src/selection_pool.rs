use crate::weighted_utxo::WeightedUtxo;
use crate::SelectionError::SolutionNotFound;
use crate::{SelectionError, Spendable};
use bitcoin_units::{Amount, FeeRate, Weight};

use crate::effective_value;
use crate::OverflowError::Addition;
use crate::SelectionError::Overflow;

/// Represents the spendable conditions of a `UTXO`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SelectionPool {
    /// The index of the provided Spendable.
    pub utxos: Vec<WeightedUtxo>,
    pub available_value: u64,
}

impl SelectionPool {
    /// Creates a new `UtxoPool`.
    pub(crate) fn new<T: Spendable>(
        spendable_coins: &[T],
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
    ) -> Result<Self, SelectionError> {
        let weighted_utxos: Vec<_> = spendable_coins
            .iter()
            .enumerate()
            .filter_map(|(index, coin)| {
                WeightedUtxo::new(
                    coin.value(),
                    coin.total_weight(),
                    fee_rate,
                    long_term_fee_rate,
                    index,
                )
            })
            .collect();

        if weighted_utxos.is_empty() {
            return Err(SolutionNotFound);
        }

        let available_value = weighted_utxos
            .iter()
            .filter_map(|u| effective_value(fee_rate, u.weight, u.value))
            .filter_map(|u| u.to_unsigned().ok())
            .try_fold(Amount::ZERO, Amount::checked_add)
            .ok_or(Overflow(Addition))?
            .to_sat();

        let _ = weighted_utxos
            .iter()
            .map(|u| u.weight)
            .try_fold(Weight::ZERO, Weight::checked_add)
            .ok_or(Overflow(Addition))?;

        Ok(Self { utxos: weighted_utxos, available_value })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::Utxo;

    #[test]
    fn pool_sums_to_less_than_max_money() {
        let amts = [Amount::MAX, Amount::from_sat_u32(1)];
        let utxos: Vec<_> =
            amts.iter().map(|a| Utxo { value: *a, weight: Weight::from_wu(230) }).collect();
        let r = SelectionPool::new(&utxos, FeeRate::ZERO, FeeRate::ZERO);
        match r {
            Ok(_) => panic!("expected panic when sum of pool exceeds Amount::MAX"),
            Err(e) => assert!(e == crate::SelectionError::Overflow(Addition)),
        }
    }

    #[test]
    fn pool_weight_sums_to_less_than_weight_max() {
        let weights = [Weight::MAX, WeightedUtxo::MIN_WEIGHT];
        let utxos: Vec<_> =
            weights.iter().map(|w| Utxo { value: Amount::from_sat_u32(42), weight: *w }).collect();

        let r = SelectionPool::new(&utxos, FeeRate::ZERO, FeeRate::ZERO);
        match r {
            Ok(_) => panic!("expected panic when sum of pool weight exceeds Weight::MAX"),
            Err(e) => assert!(e == crate::SelectionError::Overflow(Addition)),
        }
    }
}

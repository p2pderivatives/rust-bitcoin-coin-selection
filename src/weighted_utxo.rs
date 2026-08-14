use std::cmp::Ordering;

use bitcoin_units::{Amount, FeeRate, Weight};

use crate::effective_value;

/// Represents the spendable conditions of a `UTXO`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) struct WeightedUtxo {
    /// The `Amount` that the output contributes towards the selection target.
    pub(crate) value: Amount,
    /// The estimated `Weight` (satisfaction weight + base weight) of the output.
    pub(crate) weight: Weight,
    /// The positive effective value `(value - fee)`.  This value is stored as a `u64` for
    /// better performance.
    pub(crate) effective_value: u64,
    /// The `SignedAmount` required to spend the output at the given `fee_rate`.
    pub(crate) fee: i64,
    /// The `SignedAmount` required to spend the output at the given `long_term_fee_rate`.
    pub(crate) long_term_fee: i64,
    /// A metric for how wasteful it is to spend this `WeightedUtxo` given the current fee
    /// environment.
    pub(crate) waste: i64,
    /// The index of the provided Spendable.
    pub(crate) spendable_index: usize,
}

impl WeightedUtxo {
    /// Smallest UTXO that can exist in practice.
    ///
    /// 32 byte txid, 4 byte output index, 1 byte scriptSig, 4 byte sequence.
    pub(crate) const MIN_WEIGHT: Weight = Weight::from_vb_unchecked(41);

    /// Creates a new `WeightedUtxo`.
    pub(crate) fn new(
        value: Amount,
        weight: Weight,
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
        spendable_index: usize,
    ) -> Option<WeightedUtxo> {
        if weight < Self::MIN_WEIGHT {
            None
        } else if let Ok(eff) = effective_value(fee_rate, weight, value)?.to_unsigned() {
            let effective_value = eff.to_sat();
            let fee = fee_rate.to_fee(weight).to_signed().to_sat();
            let long_term_fee = long_term_fee_rate.to_fee(weight).to_signed().to_sat();
            let waste = fee - long_term_fee;
            Some(Self {
                value,
                weight,
                effective_value,
                fee,
                long_term_fee,
                waste,
                spendable_index,
            })
        } else {
            None
        }
    }

    pub(crate) fn from_spendables<T: crate::Spendable>(
        spendable_coins: &[T],
        fee_rate: FeeRate,
        lt_fee_rate: FeeRate,
    ) -> Vec<Self> {
        spendable_coins
            .iter()
            .enumerate()
            .filter_map(|(index, coin)| {
                WeightedUtxo::new(coin.value(), coin.total_weight(), fee_rate, lt_fee_rate, index)
            })
            .collect()
    }

    /// Calculates if the current fee environment is expensive.
    pub(crate) fn is_fee_expensive(&self) -> bool {
        self.fee > self.long_term_fee
    }
}

impl Ord for WeightedUtxo {
    fn cmp(&self, other: &Self) -> Ordering {
        other.effective_value.cmp(&self.effective_value).then(self.weight.cmp(&other.weight))
    }
}

impl PartialOrd for WeightedUtxo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn weighted_utxo_constructor_overflow() {
        let value = Amount::from_sat_u32(100);
        let weight = Weight::MAX;
        let fee_rate = FeeRate::MAX;
        let long_term_fee_rate = FeeRate::MAX;

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate, 0);
        assert!(utxo.is_none());
    }

    #[test]
    fn weighted_utxo_constructor_negative_eff_value() {
        let value = Amount::from_sat_u32(1);
        let weight = Weight::from_vb(68).unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(20);
        let long_term_fee_rate = FeeRate::from_sat_per_kwu(20);

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate, 0);
        assert!(utxo.is_none());
    }
}

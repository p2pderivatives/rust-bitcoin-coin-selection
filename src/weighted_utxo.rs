use std::cmp::Ordering;

use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};

use crate::effective_value;

#[derive(Debug, Clone, PartialEq, Eq)]
/// Represents the spendable conditions of a `UTXO`.
pub struct WeightedUtxo {
    /// The `Amount` that the output contributes towards the selection target.
    value: Amount,
    /// The estimated `Weight` (satisfaction weight + base weight) of the output.
    weight: Weight,
    /// The positive effective value `(value - fee)`.  This value is stored as a `u64` for
    /// better performance.
    effective_value: u64,
    /// The `SignedAmount` required to spend the output at the given `fee_rate`.
    fee: SignedAmount,
    /// The `SignedAmount` required to spend the output at the given `long_term_fee_rate`.
    long_term_fee: SignedAmount,
    /// A metric for how wasteful it is to spend this `WeightedUtxo` given the current fee
    /// environment.
    waste: i64,
}

impl WeightedUtxo {
    /// Creates a new `WeightedUtxo`.
    pub fn new(
        value: Amount,
        weight: Weight,
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
    ) -> Option<WeightedUtxo> {
        let positive_effective_value = Self::positive_effective_value(fee_rate, weight, value);

        if let Some(effective_value) = positive_effective_value {
            let fee = fee_rate.fee_wu(weight)?.to_signed();
            let long_term_fee: SignedAmount = long_term_fee_rate.fee_wu(weight)?.to_signed();
            let waste = Self::calculate_waste(fee, long_term_fee);
            return Some(Self { value, weight, effective_value, fee, long_term_fee, waste });
        }

        None
    }

    /// Calculates if the current fee environment is expensive.
    pub fn is_fee_expensive(&self) -> bool { self.fee > self.long_term_fee }

    /// Returns the associated value.
    pub fn value(&self) -> Amount { self.value }

    /// Returns the associated weight.
    pub fn weight(&self) -> Weight { self.weight }

    /// Returns the associated waste.
    pub fn waste(&self) -> SignedAmount { SignedAmount::from_sat(self.waste).unwrap() }

    /// Returns the calculated effective value.
    pub fn effective_value(&self) -> Amount { Amount::from_sat(self.effective_value).unwrap() }

    /// Returns the calculated effective value using the native type.
    pub fn effective_value_raw(&self) -> u64 { self.effective_value }

    /// Returns the calculated waste using the native type.
    pub fn waste_raw(&self) -> i64 { self.waste }

    fn positive_effective_value(fee_rate: FeeRate, weight: Weight, value: Amount) -> Option<u64> {
        if let Some(eff_value) = effective_value(fee_rate, weight, value) {
            if let Ok(unsigned) = eff_value.to_unsigned() {
                return Some(unsigned.to_sat());
            }
        }

        None
    }

    fn calculate_waste(fee: SignedAmount, long_term_fee: SignedAmount) -> i64 {
        fee.to_sat() - long_term_fee.to_sat()
    }
}

impl Ord for WeightedUtxo {
    fn cmp(&self, other: &Self) -> Ordering {
        other.effective_value.cmp(&self.effective_value).then(self.weight.cmp(&other.weight))
    }
}

impl PartialOrd for WeightedUtxo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
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

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate);
        assert!(utxo.is_none());
    }

    #[test]
    fn weighted_utxo_constructor_negative_eff_value() {
        let value = Amount::from_sat_u32(1);
        let weight = Weight::from_vb(68).unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(20);
        let long_term_fee_rate = FeeRate::from_sat_per_kwu(20);

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate);
        assert!(utxo.is_none());
    }
}

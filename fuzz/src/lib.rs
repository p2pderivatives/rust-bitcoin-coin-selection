use arbitrary::{Arbitrary, Result, Unstructured};
use bitcoin_coin_selection::WeightedUtxo;
use bitcoin_units::{Amount, FeeRate, Weight};

#[derive(Debug)]
pub struct UtxoPool {
    pub utxos: Vec<WeightedUtxo>,
}

impl<'a> Arbitrary<'a> for UtxoPool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let init: Vec<(Amount, Weight)> = Vec::arbitrary(u)?;
        let fee_rate = FeeRate::arbitrary(u).unwrap();
        let lt_fee_rate = FeeRate::arbitrary(u).unwrap();
        let utxos: Vec<WeightedUtxo> = init
            .iter()
            .filter_map(|i| WeightedUtxo::new(i.0, i.1, fee_rate, lt_fee_rate))
            .collect();

        Ok(UtxoPool { utxos })
    }
}

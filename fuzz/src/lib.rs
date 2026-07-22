use arbitrary::{Arbitrary, Result, Unstructured};
use bitcoin_coin_selection::Spendable;
use bitcoin_units::{Amount, Weight};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pool {
    pub utxos: Vec<Utxo>
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Utxo {
    pub value: Amount,
    pub weight: Weight,
}

impl Spendable for Utxo {
    fn total_weight(&self) -> Weight {
        self.weight
    }

    fn value(&self) -> Amount {
        self.value
    }
}

impl<'a> Arbitrary<'a> for Utxo {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let value = Amount::arbitrary(u)?;
        let weight = Weight::arbitrary(u)?;
        Ok(Utxo { value, weight })
    }
}

impl<'a> Arbitrary<'a> for Pool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let utxos: Vec<Utxo> = Vec::arbitrary(u)?;
        Ok(Pool { utxos })
    }
}

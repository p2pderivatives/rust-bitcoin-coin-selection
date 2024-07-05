use bitcoin::Amount;
use bitcoin_coin_selection::select_coins;
use bitcoin_coin_selection::WeightedUtxo;
use honggfuzz::fuzz;

use bitcoin::FeeRate;
use bitcoin::ScriptBuf;
use bitcoin::TxOut;
use bitcoin::Weight;

fn main() {
    loop {
        fuzz!(|data: &[u8]| {
            let mut i = 0;
            let mut target = Amount::ZERO;
            let mut pool = vec![];

            while i < 10 && i < data.len() {
                let d: u8 = data[i];

                let val: u64 = u64::from(d) * 1_000;
                let amt: Amount = Amount::from_sat(val);
                target += amt;

                let output = TxOut { value: amt, script_pubkey: ScriptBuf::new() };

                let wu = WeightedUtxo { satisfaction_weight: Weight::ZERO, utxo: output };

                pool.push(wu);

                let _coins =
                    select_coins(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &pool)
                        .unwrap();

                i += 1;
            }
        });
    }
}

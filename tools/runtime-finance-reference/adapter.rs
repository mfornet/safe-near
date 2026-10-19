// Compiled as a child module of the pinned runtime. Calls the actual private
// refund routine without changing its implementation or visibility.
use super::*;
use near_primitives::action::{CreateAccountAction, FunctionCallAction};
use near_primitives::receipt::ActionReceipt;
use serde_json::{Value, json};
use std::borrow::Cow;

pub fn execute(v: Value) -> Result<Value, Box<dyn std::error::Error>> {
    let n = |key: &str| -> Result<u64, Box<dyn std::error::Error>> {
        Ok(v[key].as_u64().ok_or("missing u64")?)
    };
    let balance = |key: &str| -> Result<Balance, Box<dyn std::error::Error>> {
        Ok(Balance::from_yoctonear(
            v[key].as_str().ok_or("missing balance")?.parse()?,
        ))
    };
    let version: u32 = n("protocolVersion")?.try_into()?;
    if !(84..=86).contains(&version) {
        return Err("financial reference supports protocol versions 84 through 86".into());
    }
    let store = near_parameters::RuntimeConfigStore::new(None);
    let config = store.get_config(version);
    let created = v["createdAccount"]
        .as_bool()
        .ok_or("missing createdAccount")?;
    let mut actions = Vec::new();
    if created {
        actions.push(Action::CreateAccount(CreateAccountAction {}));
    }
    actions.push(Action::FunctionCall(Box::new(FunctionCallAction {
        method_name: "go".into(),
        args: vec![],
        gas: Gas::from_gas(n("prepaidGas")?),
        deposit: Balance::ZERO,
    })));
    let id = "alice.near".parse()?;
    let receiver = "bob.near".parse()?;
    let key = near_crypto::PublicKey::empty(near_crypto::KeyType::ED25519);
    let current = balance("currentPrice")?;
    let purchase = balance("purchasePrice")?;
    let cost = config::calculate_tx_cost(&receiver, &id, &key, &actions, &config, current)?;
    let action = ActionReceipt {
        signer_id: id.clone(),
        signer_public_key: key,
        gas_price: purchase,
        output_data_receivers: vec![],
        input_data_ids: vec![],
        actions,
    };
    let receipt = Receipt::V0(near_primitives::receipt::ReceiptV0 {
        predecessor_id: id,
        receiver_id: receiver,
        receipt_id: Default::default(),
        receipt: ReceiptEnum::Action(action.clone()),
    });
    let action = VersionedActionReceipt::V1(Cow::Borrowed(&action));
    let mut result = ActionReceiptResult::new();
    result.gas_burnt = Gas::from_gas(n("burntGas")?);
    result.gas_used = Gas::from_gas(n("usedGas")?);
    let burn = if near_primitives::version::ProtocolFeature::AccountCostIncrease.enabled(version) {
        std::cmp::min(purchase, current)
    } else {
        current
    };
    let settlement = Runtime::new().refund_unspent_gas_and_deposits(
        burn,
        purchase,
        &receipt,
        &action,
        &mut result,
        &config,
        created,
        version,
    )?;
    let refund: u128 = result
        .new_receipts
        .iter()
        .map(|r| {
            let ReceiptEnum::Action(a) = r.receipt() else {
                panic!("unexpected refund")
            };
            let Action::Transfer(t) = &a.actions[0] else {
                panic!("unexpected refund action")
            };
            t.deposit.as_yoctonear()
        })
        .sum();
    Ok(json!({
        "txGasBurnt":cost.gas_burnt.as_gas(), "txGasRemaining":cost.gas_remaining.as_gas(),
        "txReceiptPrice":cost.receipt_gas_price.as_yoctonear().to_string(),
        "txTotal":cost.total_cost.as_yoctonear().to_string(),
        "burnPrice":burn.as_yoctonear().to_string(), "refund":refund.to_string(),
        "priceDeficit":settlement.price_deficit.as_yoctonear().to_string(),
        "priceSurplus":settlement.price_surplus.as_yoctonear().to_string(),
        "refundPenalty":settlement.refund_penalty.as_yoctonear().to_string(),
        "creationCharge":settlement.create_account_charge.as_yoctonear().to_string()
    }))
}

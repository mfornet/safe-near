// Compiled as a child module of the pinned runtime. Calls the actual private
// refund routine without changing its implementation or visibility.
use super::*;
use near_primitives::action::{CreateAccountAction, FunctionCallAction};
use near_primitives::receipt::ActionReceipt;
use serde_json::{Value, json};
use std::borrow::Cow;

pub fn execute(v: Value) -> Result<Value, Box<dyn std::error::Error>> {
    if let Some(operation) = v.get("operation") {
        return match operation.as_str() {
            Some("refundAllowance") => refund_allowance(v),
            _ => Err("unknown financial operation".into()),
        };
    }
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
    let id: near_primitives::types::AccountId = "alice.near".parse()?;
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

// Calls the actual trie-backed allowance routine, including absent/replaced keys.
fn refund_allowance(v: Value) -> Result<Value, Box<dyn std::error::Error>> {
    use near_primitives::account::{AccessKeyPermission, FunctionCallPermission};
    use near_primitives::shard_layout::ShardUId;
    use near_store::{get_access_key, set_access_key};
    let kind = v["keyKind"].as_str().ok_or("missing keyKind")?;
    let allowance: u128 = v["allowance"]
        .as_str()
        .ok_or("missing allowance")?
        .parse()?;
    let matches = v["targetMatches"]
        .as_bool()
        .ok_or("missing targetMatches")?;
    let nonce = v["keyNonce"].as_u64().ok_or("missing keyNonce")?;
    let receiver = v["receiverId"]
        .as_str()
        .ok_or("missing receiverId")?
        .to_string();
    let methods: Vec<String> = serde_json::from_value(v["methods"].clone())?;
    let refunds: Vec<Balance> = v["refunds"]
        .as_array()
        .ok_or("missing refunds")?
        .iter()
        .map(|v| {
            Ok(Balance::from_yoctonear(
                v.as_str().ok_or("bad refund")?.parse()?,
            ))
        })
        .collect::<Result<_, Box<dyn std::error::Error>>>()?;
    let target = PublicKey::ED25519(near_crypto::ED25519PublicKey([7; 32]));
    let other = PublicKey::ED25519(near_crypto::ED25519PublicKey([8; 32]));
    let stored = if matches { target.clone() } else { other };
    let id: near_primitives::types::AccountId = "alice.near".parse()?;
    let tries = near_store::test_utils::TestTriesBuilder::new().build();
    let mut state = tries.new_trie_update(ShardUId::single_shard(), Default::default());
    let permission = match kind {
        "finite" => Some(AccessKeyPermission::FunctionCall(FunctionCallPermission {
            allowance: Some(Balance::from_yoctonear(allowance)),
            receiver_id: receiver.clone(),
            method_names: methods.clone(),
        })),
        "unlimited" => Some(AccessKeyPermission::FunctionCall(FunctionCallPermission {
            allowance: None,
            receiver_id: receiver.clone(),
            method_names: methods.clone(),
        })),
        "full" => Some(AccessKeyPermission::FullAccess),
        "missing" => None,
        _ => return Err("unknown key kind".into()),
    };
    if let Some(permission) = permission {
        set_access_key(
            &mut state,
            id.clone(),
            stored.clone(),
            &AccessKey { nonce, permission },
        );
    }
    for refund in &refunds {
        actions::try_refund_allowance(&mut state, &id, &target, *refund)?;
    }
    let normalize = |key: Option<AccessKey>| -> Result<Value, Box<dyn std::error::Error>> {
        let storage_bytes = match &key {
            Some(key) => Some(borsh::to_vec(&stored)?.len() + borsh::to_vec(key)?.len()),
            None => None,
        };
        Ok(match key {
            None => Value::Null,
            Some(key) => match key.permission {
                AccessKeyPermission::FullAccess => {
                    json!({"nonce":key.nonce,"kind":"full","storageBytes":storage_bytes})
                }
                AccessKeyPermission::FunctionCall(p) => {
                    json!({"nonce":key.nonce,"kind":"functionCall",
                    "allowance":p.allowance.map(|a|a.as_yoctonear().to_string()),
                    "receiverId":p.receiver_id,"methods":p.method_names,"storageBytes":storage_bytes})
                }
                _ => return Err("unexpected gas key".into()),
            },
        })
    };
    let amount = refunds.first().copied().unwrap_or(Balance::ZERO);
    let gas = Receipt::new_gas_refund(&id, amount, target.clone());
    let balance = Receipt::new_balance_refund(&id, amount);
    let metadata = |receipt: &Receipt| -> Result<Value, Box<dyn std::error::Error>> {
        let ReceiptEnum::Action(action) = receipt.receipt() else {
            return Err("not an action".into());
        };
        Ok(
            json!({"predecessorId":receipt.predecessor_id(),"receiverId":receipt.receiver_id(),
            "signerId":action.signer_id,"signerPublicKey":borsh::to_vec(&action.signer_public_key)?,
            "gasPrice":action.gas_price.as_yoctonear().to_string(),
            "amount":match &action.actions[..] {
                [Action::Transfer(t)] => t.deposit.as_yoctonear().to_string(),
                _ => return Err("not a single transfer".into()),
            }}),
        )
    };
    Ok(
        json!({"targetKey":normalize(get_access_key(&state,&id,&target)?)?,
        "storedKey":normalize(get_access_key(&state,&id,&stored)?)?,
        "gasRefund":metadata(&gas)?,"balanceRefund":metadata(&balance)?}),
    )
}

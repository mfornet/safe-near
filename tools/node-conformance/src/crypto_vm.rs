//! The oracle for the VM's pairing and P-256 host functions: it runs `near_vm_runner`'s own `VMLogic`
//! (`alt_bn128_*`, `bls12381_*`, `p256_verify`, `near-vm-runner` =0.37.4) over a flat memory, so every
//! verdict is the host function's, wrapping and error cases included. A trap (`HostError`) is `None`.

use near_parameters::{RuntimeConfig, RuntimeFeesConfig};
use near_primitives_core::types::{Balance, Gas};
use near_vm_runner::logic::mocks::mock_external::MockedExternal;
use near_vm_runner::logic::{
    Config, ExecutionResultState, MemSlice, MemoryLike, VMContext, VMLogic, VMLogicError,
};
use std::borrow::Cow;
use std::sync::Arc;

const MEMORY: usize = 1 << 21;
const INPUT: u64 = 1 << 12;
const OUTPUT: u64 = 1 << 20;

struct Memory(Vec<u8>);

fn range(ptr: u64, len: usize) -> Result<std::ops::Range<usize>, ()> {
    let start = usize::try_from(ptr).map_err(|_| ())?;
    Ok(start..start.checked_add(len).ok_or(())?)
}

impl MemoryLike for Memory {
    fn fits_memory(&self, slice: MemSlice) -> Result<(), ()> {
        self.0.get(slice.range::<usize>()?).map(|_| ()).ok_or(())
    }

    fn view_memory(&self, slice: MemSlice) -> Result<Cow<'_, [u8]>, ()> {
        self.0.get(slice.range::<usize>()?).map(Cow::Borrowed).ok_or(())
    }

    fn read_memory(&self, ptr: u64, buffer: &mut [u8]) -> Result<(), ()> {
        buffer.copy_from_slice(self.0.get(range(ptr, buffer.len())?).ok_or(())?);
        Ok(())
    }

    fn write_memory(&mut self, ptr: u64, buffer: &[u8]) -> Result<(), ()> {
        self.0.get_mut(range(ptr, buffer.len())?).ok_or(())?.copy_from_slice(buffer);
        Ok(())
    }
}

fn context() -> VMContext {
    VMContext {
        current_account_id: "alice.near".parse().unwrap(),
        signer_account_id: "bob.near".parse().unwrap(),
        signer_account_pk: vec![0, 1, 2, 3, 4],
        predecessor_account_id: "carol.near".parse().unwrap(),
        refund_to_account_id: "david.near".parse().unwrap(),
        input: std::rc::Rc::new([0, 1, 2, 3, 4]),
        promise_results: vec![].into(),
        block_height: 10,
        block_timestamp: 42,
        epoch_height: 1,
        account_balance: Balance::from_yoctonear(100),
        storage_usage: 0,
        account_locked_balance: Balance::from_yoctonear(50),
        account_contract: near_primitives_core::account::AccountContract::None,
        attached_deposit: Balance::from_yoctonear(10),
        prepaid_gas: Gas::from_teragas(100),
        random_seed: vec![0, 1, 2],
        view_config: None,
        output_data_receivers: vec![],
    }
}

/// The host functions under the free configuration of the current protocol, with the NEP-488 fix
/// (`bls12381_not_in_group_fix`) on or off.
pub struct Vm {
    config: Arc<Config>,
    fees: Arc<RuntimeFeesConfig>,
}

/// What a call returned: the value the host function returns and the bytes it left in register 0.
pub struct Reply {
    pub ret: u64,
    pub out: Vec<u8>,
}

impl Vm {
    pub fn new(not_in_group_fix: bool) -> Vm {
        let free = RuntimeConfig::free();
        let mut config = Config::clone(&free.wasm_config);
        config.bls12381_not_in_group_fix = not_in_group_fix;
        Vm { config: Arc::new(config), fees: free.fees.clone() }
    }

    /// Run `f` on a fresh `VMLogic` whose memory holds `data` at `INPUT`; the register 0 content is
    /// read afterwards. `Err` is a trap.
    fn run(
        &self,
        data: &[&[u8]],
        f: impl FnOnce(&mut VMLogic, &[u64]) -> Result<u64, VMLogicError>,
    ) -> Option<Reply> {
        let mut memory = Memory(vec![0; MEMORY]);
        let mut ptrs = vec![];
        let mut at = INPUT;
        for d in data {
            memory.0[at as usize..at as usize + d.len()].copy_from_slice(d);
            ptrs.push(at);
            at += d.len() as u64 + 16;
        }
        let ctx = context();
        let mut ext = MockedExternal::default();
        let state =
            ExecutionResultState::new(&ctx, ctx.make_gas_counter(&self.config), self.config.clone());
        let mut logic = VMLogic::new(&mut ext, &ctx, self.fees.clone(), state, &mut memory);
        let ret = f(&mut logic, &ptrs).ok()?;
        let len = logic.register_len(0).unwrap();
        let mut out = vec![];
        if len != u64::MAX {
            logic.read_register(0, OUTPUT).unwrap();
            drop(logic);
            out = memory.0[OUTPUT as usize..OUTPUT as usize + len as usize].to_vec();
        }
        Some(Reply { ret, out })
    }

    /// `alt_bn128_g1_multiexp` and `alt_bn128_g1_sum`: the 64 bytes written, or a trap.
    pub fn bn_g1(&self, multiexp: bool, data: &[u8]) -> Option<Vec<u8>> {
        self.run(&[data], |l, p| {
            let n = data.len() as u64;
            if multiexp {
                l.alt_bn128_g1_multiexp(n, p[0], 0)
            } else {
                l.alt_bn128_g1_sum(n, p[0], 0)
            }
            .map(|()| 0)
        })
        .map(|r| r.out)
    }

    /// `alt_bn128_pairing_check`: whether the product is one, or a trap.
    pub fn bn_pairing(&self, data: &[u8]) -> Option<bool> {
        self.run(&[data], |l, p| l.alt_bn128_pairing_check(data.len() as u64, p[0])).map(|r| r.ret == 1)
    }

    /// A `bls12381_*` function by its name without the prefix; the host's return value and register.
    pub fn bls(&self, name: &str, data: &[u8]) -> Option<Reply> {
        self.run(&[data], |l, p| {
            let n = data.len() as u64;
            match name {
                "p1_sum" => l.bls12381_p1_sum(n, p[0], 0),
                "p2_sum" => l.bls12381_p2_sum(n, p[0], 0),
                "g1_multiexp" => l.bls12381_g1_multiexp(n, p[0], 0),
                "g2_multiexp" => l.bls12381_g2_multiexp(n, p[0], 0),
                "map_fp_to_g1" => l.bls12381_map_fp_to_g1(n, p[0], 0),
                "map_fp2_to_g2" => l.bls12381_map_fp2_to_g2(n, p[0], 0),
                "pairing_check" => l.bls12381_pairing_check(n, p[0]),
                "p1_decompress" => l.bls12381_p1_decompress(n, p[0], 0),
                "p2_decompress" => l.bls12381_p2_decompress(n, p[0], 0),
                _ => panic!("unknown function {name}"),
            }
        })
    }

    /// `p256_verify`: the host's return value (1 for a valid signature), or a trap.
    pub fn p256(&self, sig: &[u8], msg: &[u8], pk: &[u8]) -> Option<u64> {
        self.run(&[sig, msg, pk], |l, p| {
            l.p256_verify(sig.len() as u64, p[0], msg.len() as u64, p[1], pk.len() as u64, p[2])
        })
        .map(|r| r.ret)
    }
}

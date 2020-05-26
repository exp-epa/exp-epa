use std::hash::BuildHasher;
use std::collections::hash_map::{DefaultHasher, RandomState};

pub static mut HASH_SEED: u128 = 0;

#[derive(Clone)]
pub struct DeterministicBuildHasher {
    rs: RandomState
}

impl Default for DeterministicBuildHasher {
    fn default() -> DeterministicBuildHasher {
        //let seed = HASH_RNG.lock().unwrap().gen();
        //let u: u128 = rand::thread_rng().gen();
        let u = unsafe { HASH_SEED };
        DeterministicBuildHasher {
            rs: unsafe { std::mem::transmute(u) }
        }
    }
}

impl BuildHasher for DeterministicBuildHasher {
    type Hasher = DefaultHasher;
    fn build_hasher(&self) -> DefaultHasher {
        self.rs.build_hasher()
    }
}
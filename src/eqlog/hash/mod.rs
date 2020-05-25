#[cfg(not(feature="eqlog_deterministic_hash"))]
use std::collections::hash_map::RandomState;
#[cfg(not(feature="eqlog_deterministic_hash"))]
pub type EqlogBuildHasher = RandomState;

#[cfg(feature="eqlog_deterministic_hash")]
pub mod deterministic_hash;
#[cfg(feature="eqlog_deterministic_hash")]
pub type EqlogBuildHasher = deterministic_hash::DeterministicBuildHasher;

pub type HashSet<K> = std::collections::HashSet<K, EqlogBuildHasher>;
pub type HashMap<K, V> = std::collections::HashMap<K, V, EqlogBuildHasher>;

macro_rules! hashmap {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(hashmap!(@single $rest)),*]));

    ($($key:expr => $value:expr,)+) => { hashmap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            let _cap = hashmap!(@count $($key),*);
            let mut _map =
                ::std::collections::HashMap::with_capacity_and_hasher(
                    _cap,
                    $crate::eqlog::hashEqlogBuildHasher::default());
            $(
                let _ = _map.insert($key, $value);
            )*
            _map
        }
    };
}

macro_rules! hashset {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(hashset!(@single $rest)),*]));

    ($($key:expr,)+) => { hashset!($($key),+) };
    ($($key:expr),*) => {
        {
            let _cap = hashset!(@count $($key),*);
            let mut _set =
                ::std::collections::HashSet::with_capacity_and_hasher(
                    _cap,
                    $crate::eqlog::hash::EqlogBuildHasher::default());
            $(
                let _ = _set.insert($key);
            )*
            _set
        }
    };
}

#![recursion_limit="128"]
#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate lazy_static;
extern crate rand;
extern crate rand_chacha;

#[macro_use]
pub mod eqlog;
pub mod cwf;
pub mod lang;
pub mod cwf_checker;

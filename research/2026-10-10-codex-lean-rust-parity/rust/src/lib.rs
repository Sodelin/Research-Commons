//! Exact executable components, with explicit finite scope and independent
//! certificate checking. This crate does not admit biological input models.
#![forbid(unsafe_code)]

pub mod affine;
pub mod count;
pub mod forest;
pub mod law;
pub mod natural_cell;
pub mod polynomial;
pub mod protocol;
pub mod source_boundary;
pub mod source_calendar;
pub mod source_completion;
pub mod source_epoch;
pub mod source_fit_bank;
pub mod source_population;
pub mod source_word;

pub use num_rational::BigRational as Rational;
pub use exact_count_certificate as inherited_poisson;
pub use exact_interval_pilot as inherited_intervals;
pub use signed_nine_pair_receiver as inherited_signed_nine;

pub fn q(n: i64, d: i64) -> Rational { Rational::new(n.into(), d.into()) }
pub fn canonical(q: &Rational) -> String { format!("{}/{}", q.numer(), q.denom()) }

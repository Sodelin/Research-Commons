//! Source-linked signed pair geometry, without source/data/outer-cover admission.
//! Inputs are sealed after ordered bounded text/domain validation. Arithmetic
//! uses the unchanged independently tested interval compatibility core.
#![forbid(unsafe_code)]
use exact_interval_pilot::{integer as z, fraction as q, Error, Rational,
    ReceiverContext as C, ReceiverInterval as I, Result};

pub const FEATURES: [&str; 9] = ["AC1", "AC2", "CC1", "BC1", "BC2", "AB1", "AB2", "AA1", "BB1"];
pub const PHYSICAL: [&str; 9] = ["h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g"];
pub const RESIDUALS: [&str; 7] = ["root", "root_time", "h", "g", "AB1", "AB2", "BB1"];
pub const DOMAIN: [(&str, &str); 9] = [("1/32", "1/8"), ("1/32", "1/8"), ("1/32", "1/8"),
    ("1/2", "6"), ("1/2", "6"), ("1/2", "6"), ("1/2", "6"), ("1/2", "6"), ("1/6", "2/3")];
pub const PYTHON_PROVIDER_SHA: &str = "c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace";

const AC1: usize = 0; const AC2: usize = 1; const CC1: usize = 2;
const BC1: usize = 3; const BC2: usize = 4; const AB1: usize = 5;
const AB2: usize = 6; const AA1: usize = 7; const BB1: usize = 8;
const H: usize = 0; const U: usize = 1; const V: usize = 2; const RA: usize = 3;
const RB: usize = 4; const RC: usize = 5; const RAB: usize = 6; const RR: usize = 7; const G: usize = 8;

/// Integer configuration input; invalid ranges retain the core's ordered errors.
#[derive(Clone, Copy, Debug)]
pub struct Config { pub precision: i32, pub max_bits: i32, pub max_exp_calls: i32 }
impl Default for Config {
    fn default() -> Self { Self { precision: 96, max_bits: 4096, max_exp_calls: 24 } }
}

/// Fixed ordered endpoints. This is not a dictionary/JSON production parser.
pub type TextBox<'a> = [(&'a str, &'a str); 9];

/// No public fields/constructor accepting unvalidated rationals or contexts.
#[derive(Debug)]
pub struct Request { math: C, m0: [I; 9], m1: [I; 9], p0: [I; 9], p1: [I; 9], config: Config }

fn array(values: Vec<I>) -> Result<[I; 9]> {
    values.try_into().map_err(|_| Error("INTERNAL_ARRAY"))
}

fn parse_box(math: &C, values: &TextBox<'_>, physical: bool) -> Result<[I; 9]> {
    let mut result = Vec::with_capacity(9);
    for (i, &(lo, hi)) in values.iter().enumerate() {
        // Preserve low parse, high parse, unrounded domain check, construction.
        let lo = exact_interval_pilot::parse::receiver(lo)?;
        let hi = exact_interval_pilot::parse::receiver(hi)?;
        let (left, right) = if physical { domain(i) } else { (z(0), z(1)) };
        if !(left <= lo && lo <= hi && hi <= right) { return Err(Error("INPUT_DOMAIN")); }
        result.push(math.interval(lo, hi)?);
    }
    array(result)
}

fn domain(i: usize) -> (Rational, Rational) {
    if i <= V { (q(1, 32), q(1, 8)) }
    else if i == G { (q(1, 6), q(2, 3)) }
    else { (q(1, 2), z(6)) }
}

impl Request {
    pub fn from_ordered_text(config: Config, means0: &TextBox<'_>, means1: &TextBox<'_>,
                             physical0: Option<&TextBox<'_>>, physical1: Option<&TextBox<'_>>) -> Result<Self> {
        // Config is validated before any text parse, like Arithmetic then box.
        let math = C::new(config.precision, config.max_bits, config.max_exp_calls)?;
        let m0 = parse_box(&math, means0, false)?;
        let m1 = parse_box(&math, means1, false)?;
        let p0 = parse_box(&math, physical0.unwrap_or(&DOMAIN), true)?;
        let p1 = parse_box(&math, physical1.unwrap_or(&DOMAIN), true)?;
        Ok(Self { math, m0, m1, p0, p1, config })
    }
}

#[derive(Debug)]
pub struct Geometry { pub differences: [I; 9], pub normalized: [Rational; 9],
    pub maximum: Rational, pub signed_residuals: [I; 7] }

#[derive(Debug)]
pub struct Outcome { pub geometry: Result<Geometry>, pub scalar_exp_calls: u32, pub config: Config }
impl Outcome {
    pub fn refused(config: Config, error: Error) -> Self {
        Self { geometry: Err(error), scalar_exp_calls: 0, config }
    }
    pub fn status(&self) -> &'static str {
        match &self.geometry {
            Ok(g) if g.maximum < q(1, 20) => "CONDITIONAL_PAIR_WIDTH_CERTIFIED",
            _ => "UNKNOWN",
        }
    }
}

pub fn evaluate(request: Request) -> Outcome {
    let context = request.math.clone(); let config = request.config;
    let geometry = compute(request);
    Outcome { geometry, scalar_exp_calls: context.exp_calls(), config }
}

fn compute(request: Request) -> Result<Geometry> {
    let Request { math, mut m0, mut m1, p0, p1, .. } = request;
    for means in [&mut m0, &mut m1] {
        for value in means.iter_mut() { *value = value.meet(&math.interval(q(1, 2), z(1))?)?; }
    }
    let dm = array((0..9).map(|i| m0[i].sub(&m1[i])).collect::<Result<Vec<_>>>()?)?;
    let prior = array((0..9).map(|i| p0[i].sub(&p1[i])).collect::<Result<Vec<_>>>()?)?;
    let a_sum0 = p0[H].add(&p0[U])?; let a_sum1 = p1[H].add(&p1[U])?;
    // Reconstruct h+u again, as the Python T generator does; do not reuse A.
    let t0 = p0[H].add(&p0[U])?.add(&p0[V])?;
    let t1 = p1[H].add(&p1[U])?.add(&p1[V])?;
    let c = q(8, 3);
    let a0 = m0[AC1].mul_scalar(z(2))?.sub_scalar(z(1))?;
    let a1 = m1[AC1].mul_scalar(z(2))?.sub_scalar(z(1))?;
    let b1 = m1[AC2].mul_scalar(z(2))?.sub_scalar(z(1))?;
    if a0.lo() <= &z(0) || a1.lo() <= &z(0) { return Err(Error("ROOT_DENOMINATOR")); }
    let rho1 = b1.div(&a1.mul(&a1)?)?;
    let er = dm[AC2].mul_scalar(z(2))?.sub(
        &rho1.mul(&a0.add(&a1)?)?.mul(&dm[AC1].mul_scalar(z(2))?)?)?;
    let r0 = &p0[RR]; let r1 = &p1[RR];
    let k_numerator = r0.mul(&r0.add_scalar(z(2) * &c)?)?.mul(r1)?.mul(&r1.add_scalar(z(2) * &c)?)?;
    let k_denominator = r0.add(r1)?.add_scalar(z(2) * &c)?.mul_scalar(&c * &c)?.mul(&a0)?.mul(&a0)?;
    let k = k_numerator.div(&k_denominator)?.meet(&math.interval(z(0), z(851))?)?;
    let dr = k.neg()?.mul(&er)?.meet(&prior[RR])?;
    let jt_left = I::scalar_div(c.clone(), r0)?.add_scalar(z(1))?.mul(&dm[AC1].mul_scalar(z(2))?)?;
    let jt = jt_left.sub(&a1.mul_scalar(c.clone())?.mul(&dr)?.div(&r0.mul(r1)?)?)?;
    let dt = math.interval(q(3, 8), q(9, 8))?.neg()?.mul(&jt)?.meet(&t0.sub(&t1)?)?;
    let cc_exp = math.exp_neg(&p1[RC].mul(&t0)?)?;
    let dc = dm[CC1].sub(&cc_exp.mul(&dm[AC1])?)?
        .sub(&math.interval(-q(48, 29), q(48, 29))?.mul(&dt)?)?
        .div(&math.interval(q(3, 377), q(3, 16))?)?.meet(&prior[RC])?;
    let y0 = m0[BC1].sub(&m0[AC1])?; let y1 = m1[BC1].sub(&m1[AC1])?;
    if y0.lo() <= &z(0) || y1.lo() <= &z(0) { return Err(Error("PULSE_DENOMINATOR")); }
    let q1 = m1[BC2].sub(&m1[AC2])?.div(&y1)?;
    let eh = dm[BC2].sub(&dm[AC2])?.sub(&q1.mul(&dm[BC1].sub(&dm[AC1])?)?)?;
    let dh = math.interval(-q(16, 3), q(16, 3))?.mul(&dt)?
        .add(&math.interval(z(0), q(1, 8))?.mul(&dc)?)?
        .add(&math.interval(-q(12, 19), q(12, 19))?.mul(&dr)?)?
        .sub(&eh.div(&y0)?)?.div(&math.interval(q(4, 9), q(208, 51))?)?.meet(&prior[H])?;
    let g0 = &p0[G]; let g1 = &p1[G];
    let eg_left = dm[BC1].sub(&I::scalar_sub(z(1), g1)?.mul(&dm[AC1])?)?;
    // Preserve g1*dmCC1 before the charged exp(rC0*h0) call.
    let eg_right = g1.mul(&dm[CC1])?;
    let eg_exp = math.exp_neg(&p0[RC].mul(&p0[H])?)?;
    let eg = eg_left.sub(&eg_right.div(&eg_exp)?)?;
    let gn = math.interval(z(-24), z(24))?.mul(&dh)?
        .add(&math.interval(-q(3, 4), q(3, 4))?.mul(&dc)?)?;
    let denominator = y0.div(g0)?.meet(&math.interval(q(1, 275), z(1))?)?;
    let dg = eg.sub(&g1.mul(&gn)?.div_scalar(z(2))?)?.div(&denominator)?.meet(&prior[G])?;
    let mut e = Vec::with_capacity(2); let mut lift = Vec::with_capacity(2);
    for (ab, ac, tc, rc) in [(AB1, AC1, q(44, 19), q(48, 361)), (AB2, AC2, q(88, 35), q(96, 1225))] {
        let value = dm[ab].sub(&g0.mul(&dm[ac])?)?
            .add(&dg.mul(&m1[ab].sub(&m1[ac])?)?.div(&I::scalar_sub(z(1), g1)?)?)?;
        let lifted = value.div(&I::scalar_sub(z(1), g0)?)?
            .add(&math.interval(-tc.clone(), tc)?.mul(&dt)?)?
            .sub(&math.interval(z(0), rc)?.mul(&dr)?)?;
        e.push(value); lift.push(lifted);
    }
    let ba = z(5 * (1_i64 << 14) * 3_i64.pow(6)) * (lift[1].abs_bound() + z(2) * lift[0].abs_bound());
    let da = math.interval(-ba.clone(), ba)?.meet(&a_sum0.sub(&a_sum1)?)?;
    let bd = z(4608) * (lift[0].abs_bound() + z(3) * da.abs_bound());
    let dd = math.interval(-bd.clone(), bd)?.meet(&prior[RAB])?;
    let b_a = z(135) * (dm[AA1].abs_bound() + z(3) * e[0].abs_bound() + q(7, 4) * da.abs_bound());
    let dra = math.interval(-b_a.clone(), b_a)?.meet(&prior[RA])?;
    let b = &p1[RB]; let ea = math.exp_neg(&b.mul(&a_sum0)?)?;
    let exp_h = math.exp_neg(&b.mul(&p0[H])?)?;
    let eb = dm[BB1].sub(&I::scalar_sub(z(1), g0)?.mul(&ea)?.mul(&dm[AB1])?)?
        .sub(&g0.mul(&exp_h)?.mul(&dm[BC1])?)?
        .sub(&g0.mul(&I::scalar_sub(z(1), g0)?)?.mul(&exp_h.sub(&ea)?)?.mul(&dm[AC1])?)?;
    let b_b = z(240) * (eb.abs_bound() + q(20, 11) * da.abs_bound() + q(128, 57) * dh.abs_bound() + q(11, 8) * dg.abs_bound());
    let db = math.interval(-b_b.clone(), b_b)?.meet(&prior[RB])?;
    let differences = [dh.clone(), da.sub(&dh)?.meet(&prior[U])?, dt.sub(&da)?.meet(&prior[V])?,
                       dra, db, dc, dd, dr, dg];
    let normalized: [Rational; 9] = std::array::from_fn(|i| {
        let (left, right) = domain(i); differences[i].abs_bound() / (right - left)
    });
    let maximum = normalized.iter().max().ok_or(Error("INTERNAL_ARRAY"))?.clone();
    Ok(Geometry { differences, normalized, maximum, signed_residuals:
        [er, jt, eh, eg, e.remove(0), e.remove(0), eb] })
}

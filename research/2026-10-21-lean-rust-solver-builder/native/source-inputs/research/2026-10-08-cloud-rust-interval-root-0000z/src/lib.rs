//! Exact arithmetic compatibility pilot. No scientific/model claim is issued.
//! Forward intervals are exact between explicit dyadic sites; receiver intervals
//! are context-bound and round on every construction, after endpoint bit checks.
#![forbid(unsafe_code)]
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::{cell::Cell, fmt, rc::Rc};
pub mod parse;
pub type Rational = BigRational;
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error(pub &'static str);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(self.0) }
}
impl std::error::Error for Error {}
fn error<T>(s: &'static str) -> Result<T> { Err(Error(s)) }
pub fn integer(n: i64) -> Rational { Rational::from_integer(n.into()) }
pub fn fraction(n: i64, d: i64) -> Rational { Rational::new(n.into(), d.into()) }
pub fn bit_size(q: &Rational) -> u64 { q.numer().bits().max(q.denom().bits()) }
fn scale(bits: u32) -> BigInt { BigInt::one() << bits as usize }
/// Mathematical floor, including negative arguments (never truncation to zero).
pub fn floor(q: &Rational) -> BigInt { q.numer().div_floor(q.denom()) }
/// Mathematical ceiling, including negative arguments.
pub fn ceil(q: &Rational) -> BigInt { q.numer().div_ceil(q.denom()) }
fn down(q: &Rational, s: &BigInt) -> Rational {
    Rational::new((q.numer() * s).div_floor(q.denom()), s.clone())
}
fn up(q: &Rational, s: &BigInt) -> Rational {
    Rational::new((q.numer() * s).div_ceil(q.denom()), s.clone())
}
fn products(a: &Rational, b: &Rational, c: &Rational, d: &Rational) -> (Rational, Rational) {
    let v = [a*c, a*d, b*c, b*d];
    (v.iter().min().unwrap().clone(), v.iter().max().unwrap().clone())
}

/// Forward-provider policy: construction and ordinary operations are exact.
/// Division is deliberately scalar-only, matching the frozen Python interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForwardInterval { lo: Rational, hi: Rational }
impl ForwardInterval {
    pub fn new(lo: Rational, hi: Rational) -> Result<Self> {
        if lo > hi { return error("reversed interval"); }
        Ok(Self {lo, hi})
    }
    pub fn point(q: Rational) -> Self { Self {lo:q.clone(), hi:q} }
    pub fn lo(&self) -> &Rational { &self.lo }
    pub fn hi(&self) -> &Rational { &self.hi }
    pub fn width(&self) -> Rational { &self.hi - &self.lo }
    pub fn contains(&self, q: &Rational) -> bool { self.lo <= *q && *q <= self.hi }
    pub fn intersects(&self, b: &Self) -> bool { self.lo <= b.hi && b.lo <= self.hi }
    pub fn add(&self, b: &Self) -> Self { Self {lo:&self.lo+&b.lo, hi:&self.hi+&b.hi} }
    pub fn neg(&self) -> Self { Self {lo:-&self.hi, hi:-&self.lo} }
    pub fn sub(&self, b: &Self) -> Self { self.add(&b.neg()) }
    pub fn mul(&self, b: &Self) -> Self {
        let (lo, hi) = products(&self.lo,&self.hi,&b.lo,&b.hi); Self {lo,hi}
    }
    pub fn div_scalar(&self, q: &Rational) -> Result<Self> {
        if q.is_zero() { return error("ZERO_DIVISION"); }
        Ok(self.mul(&Self::point(q.recip())))
    }
    /// Explicit rounding site. No intermediate arithmetic bit cap is imposed by
    /// the reference forward policy. Callers must bound untrusted precision.
    pub fn dyadic(&self, bits: u32) -> Self {
        let s=scale(bits); Self {lo:down(&self.lo,&s),hi:up(&self.hi,&s)}
    }
    pub fn unit_intersection(&self) -> Result<Self> {
        Self::new(self.lo.clone().max(integer(0)),self.hi.clone().min(integer(1)))
    }
}

/// Exact scalar e^(-x) enclosure; endpoints and width match frozen exp_neg.
/// Range reduction precedes an alternating Taylor bracket, then outward
/// dyadic squaring. No floating-point computation or provider subprocess.
/// A missing memoization cache changes performance only, never call accounting.
pub fn exp_neg(x: &Rational, bits: i32) -> Result<ForwardInterval> {
    if x.is_negative() || !(8..=192).contains(&bits) {
        return error("exponential domain/precision");
    }
    if x.is_zero() { return Ok(ForwardInterval::point(integer(1))); }
    if x >= &integer(bits as i64) {
        return ForwardInterval::new(integer(0),Rational::new(BigInt::one(),scale(bits as u32)));
    }
    let mut u=x.clone(); let mut m=0u32;
    while u > integer(1) { u /= integer(2); m+=1; }
    let q=bits as u32+m+4;
    let tol=Rational::new(BigInt::one(),scale(q));
    let (mut lower,mut upper,mut s,mut term)=(integer(0),integer(1),integer(1),integer(1));
    let mut reached=false;
    for j in 1..=512 {
        term *= &u/integer(j);
        if j%2==1 { s -= &term; lower=s.clone(); }
        else { s += &term; upper=s.clone(); }
        if &upper-&lower <= tol { reached=true; break; }
    }
    if !reached { return error("Taylor term cap exceeded"); }
    let mut ans=ForwardInterval::new(lower,upper)?.dyadic(q).unit_intersection()?;
    for _ in 0..m {
        ans=ForwardInterval::new(&ans.lo*&ans.lo,&ans.hi*&ans.hi)?.dyadic(q).unit_intersection()?;
    }
    if ans.width() > Rational::new(BigInt::one(),scale(bits as u32)) {
        return error("exponential width contract failed");
    }
    Ok(ans)
}

#[derive(Debug)]
struct ReceiverState { precision: u32, max_bits:u64, max_exp_calls:u32, exp_calls:Cell<u32> }
/// Clone shares identity and deterministic exponential-call count. A fresh
/// context, even with the same configuration, cannot mix intervals with it.
#[derive(Clone, Debug)]
pub struct ReceiverContext(Rc<ReceiverState>);
impl ReceiverContext {
    pub fn new(precision:i32,max_bits:i32,max_exp_calls:i32) -> Result<Self> {
        if !(64..=128).contains(&precision) { return error("PRECISION"); }
        if !(256..=16384).contains(&max_bits) { return error("BIT_BUDGET"); }
        if !(0..=32).contains(&max_exp_calls) { return error("EXP_BUDGET"); }
        Ok(Self(Rc::new(ReceiverState {precision:precision as u32,max_bits:max_bits as u64,
            max_exp_calls:max_exp_calls as u32,exp_calls:Cell::new(0)})))
    }
    pub fn precision(&self) -> u32 { self.0.precision }
    pub fn max_bits(&self) -> u64 { self.0.max_bits }
    pub fn exp_calls(&self) -> u32 { self.0.exp_calls.get() }
    pub fn same_context(&self, b:&Self) -> bool { Rc::ptr_eq(&self.0,&b.0) }
    pub fn check(&self,q:&Rational) -> Result<()> {
        if bit_size(q)>self.0.max_bits { return error("ARITHMETIC_BITS"); } Ok(())
    }
    pub fn interval(&self,lo:Rational,hi:Rational) -> Result<ReceiverInterval> {
        // Preserve order: empty first, reduced endpoint bit budgets, then round.
        if lo>hi { return error("EMPTY_INTERVAL"); }
        self.check(&lo)?; self.check(&hi)?;
        let s=scale(self.0.precision);
        Ok(ReceiverInterval {context:self.clone(),lo:down(&lo,&s),hi:up(&hi,&s)})
    }
    pub fn point(&self,q:Rational) -> Result<ReceiverInterval> { self.interval(q.clone(),q) }
    pub fn exp_neg(&self,x:&ReceiverInterval) -> Result<ReceiverInterval> {
        x.require_context(self)?;
        if x.lo.is_negative() { return error("EXP_DOMAIN"); }
        let calls=self.0.exp_calls.get();
        if calls+2>self.0.max_exp_calls { return error("EXP_CALLS"); }
        // Calls are charged before invoking either endpoint, even on failure.
        self.0.exp_calls.set(calls+2);
        let lo=exp_neg(&x.hi,self.0.precision as i32+4)?.lo;
        let hi=exp_neg(&x.lo,self.0.precision as i32+4)?.hi;
        self.interval(lo,hi)
    }
    pub fn exp_neg_scalar(&self,x:Rational) -> Result<ReceiverInterval> {
        self.exp_neg(&self.point(x)?)
    }
}

/// Signed receiver policy: every construction performs bit checks then outward
/// rounding. Even reciprocal construction is a distinct rounding/check site.
#[derive(Clone, Debug)]
pub struct ReceiverInterval {context:ReceiverContext,lo:Rational,hi:Rational}
impl ReceiverInterval {
    pub fn lo(&self) -> &Rational { &self.lo }
    pub fn hi(&self) -> &Rational { &self.hi }
    pub fn context(&self) -> &ReceiverContext { &self.context }
    fn require_context(&self,c:&ReceiverContext) -> Result<()> {
        if !self.context.same_context(c) { return error("ARITHMETIC_CONTEXT"); } Ok(())
    }
    pub fn add(&self,b:&Self) -> Result<Self> {
        b.require_context(&self.context)?;
        self.context.interval(&self.lo+&b.lo,&self.hi+&b.hi)
    }
    pub fn neg(&self) -> Result<Self> { self.context.interval(-&self.hi,-&self.lo) }
    pub fn sub(&self,b:&Self) -> Result<Self> {
        b.require_context(&self.context)?; self.add(&b.neg()?)
    }
    pub fn mul(&self,b:&Self) -> Result<Self> {
        b.require_context(&self.context)?;
        let (lo,hi)=products(&self.lo,&self.hi,&b.lo,&b.hi); self.context.interval(lo,hi)
    }
    pub fn div(&self,b:&Self) -> Result<Self> {
        b.require_context(&self.context)?;
        if b.lo<=integer(0) && b.hi>=integer(0) { return error("DENOMINATOR"); }
        self.mul(&self.context.interval(b.hi.recip(),b.lo.recip())?)
    }
    pub fn meet(&self,b:&Self) -> Result<Self> {
        b.require_context(&self.context)?;
        self.context.interval(self.lo.clone().max(b.lo.clone()),self.hi.clone().min(b.hi.clone()))
    }
    pub fn abs_bound(&self) -> Rational { self.lo.abs().max(self.hi.abs()) }
    pub fn add_scalar(&self,q:Rational) -> Result<Self> { self.add(&self.context.point(q)?) }
    pub fn sub_scalar(&self,q:Rational) -> Result<Self> { self.sub(&self.context.point(q)?) }
    pub fn mul_scalar(&self,q:Rational) -> Result<Self> { self.mul(&self.context.point(q)?) }
    pub fn div_scalar(&self,q:Rational) -> Result<Self> { self.div(&self.context.point(q)?) }
    pub fn scalar_sub(q:Rational,b:&Self) -> Result<Self> { b.context.point(q)?.add(&b.neg()?) }
    pub fn scalar_div(q:Rational,b:&Self) -> Result<Self> { b.context.point(q)?.div(b) }
}

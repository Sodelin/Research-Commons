//! Bounded tab-separated differential-test adapter, not a production protocol.
use exact_interval_pilot::{self as core, ForwardInterval as F, Rational, ReceiverContext as C, Error, Result};
use num_bigint::BigInt;
use num_traits::Zero;
use std::io::{self, BufRead, Write};
fn q(s:&str)->Result<Rational> {
    let mut p=s.split('/'); let n=p.next().unwrap(); let d=p.next().unwrap_or("1");
    if p.next().is_some() || s.len()>8192 {return Err(Error("PROBE_RATIONAL"));}
    let parse=|s:&str| BigInt::parse_bytes(s.as_bytes(),10).ok_or(Error("PROBE_RATIONAL"));
    let (n,d)=(parse(n)?,parse(d)?); if d.is_zero(){return Err(Error("PROBE_RATIONAL"));}
    Ok(Rational::new(n,d))
}
fn i(s:&str)->Result<i32>{s.parse().map_err(|_|Error("PROBE_INTEGER"))}
fn ff(v:&[&str])->Result<F>{F::new(q(v[0])?,q(v[1])?)}
fn pair(a:&Rational,b:&Rational)->String{format!("{a}\t{b}")}
fn run(v:&[&str],calls:&mut u32)->Result<String>{
    match v[0] {
        "parse-r" if v.len()==2 => Ok(core::parse::receiver(v[1])?.to_string()),
        "parse-f" if v.len()==2 => Ok(core::parse::forward(v[1])?.to_string()),
        "exp" if v.len()==3 => {let a=core::exp_neg(&q(v[2])?,i(v[1])?)?; Ok(pair(a.lo(),a.hi()))},
        "f" if v.len()==8 => {
            let a=ff(&v[2..4])?; let b=ff(&v[4..6])?;
            let a=match v[1] {
                "new"=>a,"add"=>a.add(&b),"sub"=>a.sub(&b),"neg"=>a.neg(),"mul"=>a.mul(&b),
                "div"=>a.div_scalar(&q(v[6])?)?,"unit"=>a.unit_intersection()?,
                "dyadic"=>{let bits=i(v[7])?;if bits<0 {return Err(Error("negative shift count"));} if bits>16384 {return Err(Error("PROBE_BITS"));}a.dyadic(bits as u32)},
                "contains"=>return Ok(if a.contains(&q(v[6])?){"true"}else{"false"}.into()),
                "intersects"=>return Ok(if a.intersects(&b){"true"}else{"false"}.into()),
                _=>return Err(Error("PROBE_OPERATION"))}; Ok(pair(a.lo(),a.hi()))
        },
        "r" if v.len()==10 => {
            let c=C::new(i(v[1])?,i(v[2])?,i(v[3])?)?;
            let result=(||{
                let a=c.interval(q(v[5])?,q(v[6])?)?;
                let b=c.interval(q(v[7])?,q(v[8])?)?;
                let a=match v[4] {
                    "new"=>a,"add"=>a.add(&b)?,"sub"=>a.sub(&b)?,"neg"=>a.neg()?,
                    "mul"=>a.mul(&b)?,"div"=>a.div(&b)?,"meet"=>a.meet(&b)?,
                    "add_scalar"=>a.add_scalar(q(v[9])?)?,"sub_scalar"=>a.sub_scalar(q(v[9])?)?,
                    "mul_scalar"=>a.mul_scalar(q(v[9])?)?,"div_scalar"=>a.div_scalar(q(v[9])?)?,
                    "scalar_sub"=>core::ReceiverInterval::scalar_sub(q(v[9])?,&a)?,
                    "scalar_div"=>core::ReceiverInterval::scalar_div(q(v[9])?,&a)?,
                    "abs"=>return Ok(a.abs_bound().to_string()),
                    "exp"=>c.exp_neg(&a)?,
                    "exp_repeat"=>{let n=i(v[9])?;if !(1..=18).contains(&n){return Err(Error("PROBE_REPETITIONS"));} let mut b=a.clone();for _ in 0..n{b=c.exp_neg(&a)?;}b},
                    "mixed"=>a.add(&C::new(i(v[1])?,i(v[2])?,i(v[3])?)?.point(core::integer(0))?)?,
                    _=>return Err(Error("PROBE_OPERATION"))};
                Ok(pair(a.lo(),a.hi()))
            })(); *calls=c.exp_calls(); result
        },
        _=>Err(Error("PROBE_SHAPE"))
    }
}
fn main(){
    let mut out=io::BufWriter::new(io::stdout().lock());
    for line in io::stdin().lock().lines(){
        let line=match line {Ok(x)=>x,Err(_)=>break};
        if line.len()>131072 {writeln!(out,"ERR\tPROBE_LINE\t0").unwrap(); continue;}
        let mut calls=0;
        let result=run(&line.split('\t').collect::<Vec<_>>(),&mut calls);
        match result {Ok(s)=>writeln!(out,"OK\t{s}\t{calls}"),Err(e)=>writeln!(out,"ERR\t{e}\t{calls}")}.unwrap();
    }
}

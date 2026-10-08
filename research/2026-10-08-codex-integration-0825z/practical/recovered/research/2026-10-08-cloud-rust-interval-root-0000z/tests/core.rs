use exact_interval_pilot::*;
use num_bigint::BigInt;
use num_traits::One;
fn f(n:i64,d:i64)->Rational {fraction(n,d)}
#[test] fn directed_negative_rounding(){
    assert_eq!(floor(&f(-7,3)),(-3).into()); assert_eq!(ceil(&f(-7,3)),(-2).into());
    let a=ForwardInterval::new(f(-7,3),f(-1,3)).unwrap().dyadic(2);
    assert_eq!(a.lo(),&f(-5,2));assert_eq!(a.hi(),&f(-1,4));
}
#[test] fn policies_are_distinct(){
    let c=ReceiverContext::new(64,256,0).unwrap(); let a=c.point(f(1,3)).unwrap();
    assert!(a.lo()<&f(1,3)); assert!(a.hi()>&f(1,3));
    let exact=ForwardInterval::point(f(1,3));assert_eq!(exact.lo(),exact.hi());
}
#[test] fn receiver_rounds_reciprocal_before_product(){
    let c=ReceiverContext::new(64,256,0).unwrap(); let a=c.point(f(-2,1)).unwrap();
    let b=c.interval(f(-7,1),f(-3,1)).unwrap(); let quotient=a.div(&b).unwrap();
    let reciprocal=c.interval(f(-1,3),f(-1,7)).unwrap(); let manual=a.mul(&reciprocal).unwrap();
    assert_eq!(quotient.lo(),manual.lo()); assert_eq!(quotient.hi(),manual.hi());
}
#[test] fn context_identity_and_clone(){
    let a=ReceiverContext::new(64,256,0).unwrap(); let b=ReceiverContext::new(64,256,0).unwrap();
    let x=a.point(integer(1)).unwrap();let y=b.point(integer(1)).unwrap();
    assert_eq!(x.add(&y).unwrap_err().0,"ARITHMETIC_CONTEXT");
    assert!(x.add(&a.clone().point(integer(1)).unwrap()).is_ok());
}
#[test] fn constructor_refusal_order(){
    let c=ReceiverContext::new(64,256,0).unwrap();
    let huge=Rational::from_integer(BigInt::one()<<256);
    assert_eq!(c.interval(huge.clone(),integer(0)).unwrap_err().0,"EMPTY_INTERVAL");
    assert_eq!(c.point(huge).unwrap_err().0,"ARITHMETIC_BITS");
    assert_eq!(ReceiverContext::new(63,0,-1).unwrap_err().0,"PRECISION");
    assert_eq!(ReceiverContext::new(64,0,-1).unwrap_err().0,"BIT_BUDGET");
}
#[test] fn budget_checked_before_rounding_not_after(){
    let c=ReceiverContext::new(128,256,0).unwrap();
    // 2^255/3 is reduced and non-dyadic, with a 256-bit input numerator.
    // Unlike the original (2^256-1)/3 integer, it exercises rounding growth.
    let v=Rational::new(BigInt::one()<<255,BigInt::from(3));
    assert_eq!(bit_size(&v),256);
    assert_eq!(v.denom(),&BigInt::from(3));
    let a=c.point(v).unwrap();
    assert!(bit_size(a.lo())>256); // post-rounding growth is intentionally allowed
    assert_eq!(a.neg().unwrap_err().0,"ARITHMETIC_BITS");
}
#[test] fn division_and_empty_meet(){
    let c=ReceiverContext::new(64,256,0).unwrap();let a=c.point(integer(1)).unwrap();
    for (l,h) in [(-1,1),(0,1),(-1,0),(0,0)] {
        assert_eq!(a.div(&c.interval(integer(l),integer(h)).unwrap()).unwrap_err().0,"DENOMINATOR");
    }
    assert_eq!(a.meet(&c.point(integer(2)).unwrap()).unwrap_err().0,"EMPTY_INTERVAL");
    assert_eq!(ForwardInterval::point(integer(1)).div_scalar(&integer(0)).unwrap_err().0,"ZERO_DIVISION");
}
#[test] fn exponential_call_count_includes_repeated_endpoints(){
    let c=ReceiverContext::new(64,256,3).unwrap();let x=c.point(integer(0)).unwrap();
    assert_eq!(c.exp_neg(&x).unwrap().lo(),&integer(1));assert_eq!(c.exp_calls(),2);
    assert_eq!(c.exp_neg(&x).unwrap_err().0,"EXP_CALLS");assert_eq!(c.exp_calls(),2);
    assert_eq!(c.exp_neg_scalar(integer(-1)).unwrap_err().0,"EXP_DOMAIN");assert_eq!(c.exp_calls(),2);
}
#[test] fn scalar_exp_domains_and_exact_shortcut(){
    assert_eq!(exp_neg(&integer(0),8).unwrap().lo(),&integer(1));
    for bits in [8,64,128,192] {
        let x=exp_neg(&integer(bits as i64),bits).unwrap();
        assert_eq!(x.lo(),&integer(0));assert_eq!(x.hi(),&Rational::new(1.into(),BigInt::one()<<bits as usize));
    }
    for bits in [-1,7,193] { assert_eq!(exp_neg(&integer(1),bits).unwrap_err().0,"exponential domain/precision"); }
}
#[test] fn parser_policies_and_unicode(){
    assert_eq!(parse::receiver("1/01").unwrap(),integer(1));assert!(parse::forward("1/01").is_err());
    assert!(parse::receiver("١/2").is_err());assert_eq!(parse::forward("١/2").unwrap(),f(1,2));
    assert_eq!(parse::forward("1/1٢").unwrap(),f(1,12));assert!(parse::forward("1/١٢").is_err());
    let huge="9".repeat(78);let reduced=format!("{huge}/{huge}");
    assert_eq!(parse::receiver(&reduced).unwrap_err().0,"INPUT_BITS");
    assert_eq!(parse::forward(&reduced).unwrap(),integer(1));
    assert_eq!(parse::receiver("1/0").unwrap_err().0,"ZERO_DENOMINATOR");
}

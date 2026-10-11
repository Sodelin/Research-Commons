use exact_interval_pilot::*;
use num_bigint::BigInt;
use num_traits::One;
use std::{cell::RefCell, rc::Rc};

#[test]
fn exact_values_precision_and_range_boundaries() {
    let mut cache=ExpCache::new(256,256);
    for bits in [8,64,128,192] {
        for x in [integer(0),fraction(1,3),fraction(999,1000),integer(1),fraction(1001,1000),
                  integer(2),fraction(2001,1000),fraction(2*bits as i64-1,2),integer(bits as i64),integer(bits as i64+1)] {
            let expected=exp_neg(&x,bits);
            assert_eq!(cache.exp_neg(&x,bits),expected);
            let before=cache.stats();
            assert_eq!(cache.exp_neg(&x,bits),expected);
            assert_eq!(cache.stats().hits,before.hits+1);
            assert_eq!(cache.stats().work,before.work);
        }
    }
    // BigRational canonicalization makes 2/6 and 1/3 the same key.
    let before=cache.stats();
    cache.exp_neg(&fraction(2,6),128).unwrap();
    assert_eq!(cache.stats().hits,before.hits+1);
    for bits in [-1,7,193] {
        assert_eq!(cache.exp_neg(&integer(0),bits),exp_neg(&integer(0),bits));
    }
    assert_eq!(cache.exp_neg(&integer(-1),128),exp_neg(&integer(-1),128));
}

#[test]
fn bounded_fifo_bypass_and_failures() {
    let mut cache=ExpCache::new(2,8);
    for n in [0,1,0,2,0] { assert_eq!(cache.exp_neg(&integer(n),8),exp_neg(&integer(n),8)); }
    assert_eq!(cache.len(),2);
    assert_eq!(cache.stats().hits,1); // Hits do not alter FIFO order.
    assert_eq!(cache.stats().evictions,2);
    let huge=Rational::from_integer(BigInt::one()<<256);
    let before=cache.stats();
    assert_eq!(cache.exp_neg(&huge,8),exp_neg(&huge,8));
    assert_eq!(cache.stats().bypasses,before.bypasses+1);
    assert_eq!(cache.len(),2);
    let before=cache.stats();
    assert!(cache.exp_neg(&integer(-1),8).is_err());
    assert_eq!(cache.stats(),before);
    let mut disabled=ExpCache::new(0,256);
    for _ in 0..2 { assert_eq!(disabled.exp_neg(&fraction(1,3),192),exp_neg(&fraction(1,3),192)); }
    assert!(disabled.is_empty());
    assert_eq!(disabled.stats().bypasses,2);
}

#[test]
fn charging_cutoffs_and_validation_precede_hits() {
    let cache=Rc::new(RefCell::new(ExpCache::new(8,256)));
    cache.borrow_mut().exp_neg(&integer(0),68).unwrap(); // Warm scalar result.
    for budget in 0..=5 {
        let c=ReceiverContext::new_with_cache(64,256,budget,cache.clone()).unwrap();
        let u=ReceiverContext::new(64,256,budget).unwrap();
        let x=c.point(integer(0)).unwrap(); let y=u.point(integer(0)).unwrap();
        for _ in 0..4 {
            let before=cache.borrow().stats();
            let a=c.exp_neg(&x); let b=u.exp_neg(&y);
            match (a,b) {
                (Ok(a),Ok(b))=>{assert_eq!(a.lo(),b.lo());assert_eq!(a.hi(),b.hi());assert!(a.context().same_context(&c));},
                (Err(a),Err(b))=>{assert_eq!(a,b);assert_eq!(cache.borrow().stats(),before);},
                _=>panic!("cached/uncached status mismatch"),
            }
            assert_eq!(c.exp_calls(),u.exp_calls());
        }
        let before=cache.borrow().stats();
        assert_eq!(c.exp_neg(&u.point(integer(-1)).unwrap()).unwrap_err().0,"ARITHMETIC_CONTEXT");
        assert_eq!(c.exp_neg_scalar(integer(-1)).unwrap_err().0,"EXP_DOMAIN");
        assert_eq!(cache.borrow().stats(),before);
    }
}

#[test]
fn shared_plain_values_keep_contexts_and_budgets_independent() {
    let cache=Rc::new(RefCell::new(ExpCache::new(8,512)));
    let a=ReceiverContext::new_with_cache(128,256,4,cache.clone()).unwrap();
    let b=ReceiverContext::new_with_cache(128,512,2,cache.clone()).unwrap();
    let x=a.exp_neg_scalar(fraction(1,3)).unwrap();
    let before=cache.borrow().stats();
    let y=b.exp_neg_scalar(fraction(1,3)).unwrap();
    assert_eq!(x.lo(),y.lo()); assert_eq!(x.hi(),y.hi());
    assert_eq!(cache.borrow().stats().hits,before.hits+2);
    assert_eq!(a.exp_calls(),2);assert_eq!(b.exp_calls(),2);
    assert_eq!(x.add(&y).unwrap_err().0,"ARITHMETIC_CONTEXT");
    let cloned=a.clone();
    assert!(cloned.exp_neg_scalar(fraction(1,3)).is_ok());
    assert_eq!(a.exp_calls(),4);
    assert_eq!(b.exp_neg_scalar(fraction(1,3)).unwrap_err().0,"EXP_CALLS");
    assert_eq!(b.exp_calls(),2);
}

#[test]
fn independent_exact_taylor_and_dyadic_control() {
    // Independent integer alternating sum at x=1, with 32! common denominator.
    let mut factorial=BigInt::one();
    for j in 1..=32 { factorial*=j; }
    let mut sum=BigInt::from(0); let mut current=BigInt::one();
    for j in 0..=32 {
        if j>0 { current*=j; }
        let term=&factorial/&current;
        if j%2==0 { sum+=term; } else { sum-=term; }
    }
    let upper=Rational::new(sum.clone(),factorial.clone());
    let lower=Rational::new(sum-BigInt::one(),factorial);
    let mut cache=ExpCache::new(4,256);
    let result=cache.exp_neg(&integer(1),64).unwrap();
    assert!(result.lo()<=&lower && &upper<=result.hi());
    assert!(result.width()<=Rational::new(1.into(),BigInt::one()<<64));
    assert_eq!(cache.exp_neg(&integer(0),64).unwrap(),ForwardInterval::point(integer(1)));
    let shortcut=cache.exp_neg(&integer(64),64).unwrap();
    assert_eq!(shortcut.lo(),&integer(0));
    assert_eq!(shortcut.hi(),&Rational::new(1.into(),BigInt::one()<<64));
}

#[test]
fn held_cache_borrows_fall_back_without_new_refusals() {
    let cache=Rc::new(RefCell::new(ExpCache::new(8,256)));
    let c=ReceiverContext::new_with_cache(64,256,4,cache.clone()).unwrap();
    let u=ReceiverContext::new(64,256,4).unwrap();
    let x=c.point(fraction(1,3)).unwrap();let y=u.point(fraction(1,3)).unwrap();
    let immutable=cache.borrow();
    let a=c.exp_neg(&x).unwrap();let b=u.exp_neg(&y).unwrap();
    assert_eq!(a.lo(),b.lo());assert_eq!(a.hi(),b.hi());
    assert_eq!(immutable.stats(),CacheStats::default());
    drop(immutable);
    let mutable=cache.borrow_mut();
    let a=c.exp_neg(&x).unwrap();let b=u.exp_neg(&y).unwrap();
    assert_eq!(a.lo(),b.lo());assert_eq!(a.hi(),b.hi());
    assert_eq!(mutable.stats(),CacheStats::default());
    assert_eq!(c.exp_calls(),4);assert_eq!(u.exp_calls(),4);
    assert_eq!(c.exp_neg(&x).unwrap_err().0,"EXP_CALLS");
}

#[test]
fn deterministic_generated_endpoints_and_budget_sequences() {
    let cache=Rc::new(RefCell::new(ExpCache::new(7,512)));
    let mut seed=0x2130_2026_1011_u64;
    for case in 0..128 {
        seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let n=(seed%4096) as i64;let d=((seed>>12)%63+1) as i64;
        let precision=if case%2==0{64}else{128};let budget=(case%7) as i32;
        let c=ReceiverContext::new_with_cache(precision,256,budget,cache.clone()).unwrap();
        let u=ReceiverContext::new(precision,256,budget).unwrap();
        let x=c.interval(fraction(n,d),fraction(n+1,d)).unwrap();
        let y=u.interval(fraction(n,d),fraction(n+1,d)).unwrap();
        for _ in 0..4 {
            match (c.exp_neg(&x),u.exp_neg(&y)) {
                (Ok(a),Ok(b))=>{assert_eq!(a.lo(),b.lo());assert_eq!(a.hi(),b.hi());},
                (Err(a),Err(b))=>assert_eq!(a,b),_=>panic!("generated refinement mismatch"),
            }
            assert_eq!(c.exp_calls(),u.exp_calls());assert!(cache.borrow().len()<=7);
        }
    }
}

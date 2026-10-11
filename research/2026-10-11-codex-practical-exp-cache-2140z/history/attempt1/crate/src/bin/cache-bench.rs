//! Linux task-local allocation/CPU instrumentation; outside the safe interval lib.
//! Workloads are synthetic. Parsing and output encoding are outside timed kernels.
use exact_interval_pilot::*;
use std::{alloc::{GlobalAlloc, Layout, System}, hint::black_box, sync::atomic::{AtomicU64, Ordering}, time::Instant};

struct CountedSystem;
static EVENTS: AtomicU64=AtomicU64::new(0);
static REQUESTED: AtomicU64=AtomicU64::new(0);
static LIVE: AtomicU64=AtomicU64::new(0);
static PEAK: AtomicU64=AtomicU64::new(0);
fn allocated(size:usize) {
    EVENTS.fetch_add(1,Ordering::Relaxed);
    REQUESTED.fetch_add(size as u64,Ordering::Relaxed);
    let live=LIVE.fetch_add(size as u64,Ordering::Relaxed)+size as u64;
    PEAK.fetch_max(live,Ordering::Relaxed);
}
// Delegates identical layouts/pointers to System; counters do not alter results.
unsafe impl GlobalAlloc for CountedSystem {
    unsafe fn alloc(&self,layout:Layout)->*mut u8 {
        let p=System.alloc(layout); if !p.is_null(){allocated(layout.size());} p
    }
    unsafe fn alloc_zeroed(&self,layout:Layout)->*mut u8 {
        let p=System.alloc_zeroed(layout); if !p.is_null(){allocated(layout.size());} p
    }
    unsafe fn dealloc(&self,p:*mut u8,layout:Layout) {
        LIVE.fetch_sub(layout.size() as u64,Ordering::Relaxed); System.dealloc(p,layout);
    }
    unsafe fn realloc(&self,p:*mut u8,layout:Layout,size:usize)->*mut u8 {
        let q=System.realloc(p,layout,size);
        if !q.is_null(){LIVE.fetch_sub(layout.size() as u64,Ordering::Relaxed);allocated(size);} q
    }
}
#[global_allocator] static ALLOCATOR:CountedSystem=CountedSystem;

#[repr(C)] struct Timespec { sec:std::os::raw::c_long, nsec:std::os::raw::c_long }
unsafe extern "C" { fn clock_gettime(id:std::os::raw::c_int,t:*mut Timespec)->std::os::raw::c_int; }
fn cpu_ns()->u64 {
    let mut t=Timespec{sec:0,nsec:0};
    assert_eq!(unsafe{clock_gettime(2,&mut t)},0); // Linux CLOCK_PROCESS_CPUTIME_ID.
    t.sec as u64*1_000_000_000+t.nsec as u64
}

fn main() {
    let a:Vec<String>=std::env::args().skip(1).collect();
    assert_eq!(a.len(),4,"workload capacity repetitions calls");
    let capacity:usize=a[1].parse().unwrap();
    let reps:usize=a[2].parse().unwrap();let count:usize=a[3].parse().unwrap();
    assert!(capacity<=4096 && reps<=100 && (1..=4096).contains(&count));
    let inputs:Vec<Rational>=(0..count).map(|i|match a[0].as_str(){
        "repeated-1"=>fraction(1,3),"repeated-8"=>fraction((i%8+1) as i64,9),
        "unique"=>fraction((i+1) as i64,count as i64+1),
        "shortcut"=>integer(128+(i%8) as i64),_=>panic!("unknown workload")
    }).collect();
    // Exact outputs written once, after measurement, for independent SHA checking.
    println!("rep\twall_ns\tcpu_ns\talloc_events\trequested_bytes\tpeak_extra_live\thits\tmisses\tbypasses\tevaluations\ttaylor_terms\tsquarings\tevictions");
    for rep in 0..reps {
        let mut cache=ExpCache::new(capacity,16384);
        let mut outputs=Vec::with_capacity(count);
        let live0=LIVE.load(Ordering::Relaxed);PEAK.store(live0,Ordering::Relaxed);
        let e0=EVENTS.load(Ordering::Relaxed);let b0=REQUESTED.load(Ordering::Relaxed);
        let cpu0=cpu_ns();let start=Instant::now();
        for x in &inputs {outputs.push(black_box(cache.exp_neg(black_box(x),128).unwrap()));}
        let wall=start.elapsed().as_nanos();let cpu=cpu_ns()-cpu0;
        let events=EVENTS.load(Ordering::Relaxed)-e0;let bytes=REQUESTED.load(Ordering::Relaxed)-b0;
        let peak=PEAK.load(Ordering::Relaxed)-live0;let s=cache.stats();
        println!("{rep}\t{wall}\t{cpu}\t{events}\t{bytes}\t{peak}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",s.hits,s.misses,s.bypasses,s.work.evaluations,s.work.taylor_terms,s.work.squarings,s.evictions);
        if rep==0 {for v in &outputs {eprintln!("{}\t{}",v.lo(),v.hi());}}
        black_box(outputs);
    }
}

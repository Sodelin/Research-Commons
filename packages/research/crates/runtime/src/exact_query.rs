//! Bounded Rust integration of the RETAINED supplied-circle rectangle search.
//! Algorithm: sparse_quartet.py, Git blob49933337ce26ce0d5ef58bbfa458bf5706d8e817.
//! Only the complete displayed-topology-set oracle is admitted here. A local
//! mask check is not global graph/source admission. Limits are UNKNOWN.
//! Unknown-order learning and exact finite minimax remain separate suppliers.
use std::collections::{BTreeMap, BTreeSet};

pub type Quartet = [u64; 4];
pub type GapPair = [usize; 2];

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub taxa: usize,
    pub unique_queries: usize,
    pub predicates: usize,
    pub output_splits: usize,
    pub pending: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { taxa: 4096, unique_queries: 65536, predicates: 262144,
            output_splits: 65536, pending: 256 }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub enum Error<E> {
    Invalid(&'static str),
    Unknown(&'static str),
    Oracle(E),
}
#[derive(Debug, PartialEq, Eq)]
pub struct Recovery {
    /// Positions in the supplied original common circle, NEVER sorted taxa.
    /// [i,j] represents the bipartition with side circle[i+1..=j].
    pub gap_pairs: Vec<GapPair>,
    /// Original-label sorted quartets and original 1/2/4 masks.
    pub cache: BTreeMap<Quartet, u8>,
    pub rectangle_tests: usize,
    pub positive_internal_nodes: usize,
    pub max_search_depth: usize,
}

/// The OLD bit convention on a SORTED quartet. Complementing a two-element
/// shore preserves the bit; numeric taxon labels never become circle positions.
fn pair_bit<E>(q: Quartet, mut pair: [u64; 2]) -> Result<u8, Error<E>> {
    if !pair.contains(&q[0]) {
        let mut other = q.into_iter().filter(|x| !pair.contains(x));
        pair = [other.next().ok_or(Error::Invalid("quartet pair"))?,
            other.next().ok_or(Error::Invalid("quartet complement"))?];
    }
    let partner = if pair[0] == q[0] { pair[1] } else { pair[0] };
    match q.iter().position(|x| *x == partner) {
        Some(1) => Ok(1),
        Some(2) => Ok(2),
        Some(3) => Ok(4),
        _ => Err(Error::Invalid("quartet pair membership")),
    }
}

/// Original-label bit mask -> supplied-circle-position mask, by the actual
/// bipartitions (the OLD recover_all.remap_answer contract).
pub fn remap_support<E>(circle_quartet: Quartet, original_mask: u8) -> Result<u8, Error<E>> {
    let mut sorted = circle_quartet;
    sorted.sort_unstable();
    if sorted.windows(2).any(|w| w[0] == w[1]) {
        return Err(Error::Invalid("distinct quartet labels"));
    }
    if !(1..=7).contains(&original_mask) {
        return Err(Error::Invalid("nonempty resolved support mask"));
    }
    let mut remapped = 0;
    for j in 1..4 {
        if original_mask & pair_bit::<E>(sorted, [circle_quartet[0],circle_quartet[j]])? != 0 {
            remapped |= 1 << (j-1);
        }
    }
    if remapped & 2 != 0 {
        return Err(Error::Invalid("support crosses the supplied circle"));
    }
    Ok(remapped)
}

struct Search<'a, F> {
    circle: &'a [u64],
    oracle: F,
    limits: Limits,
    result: Recovery,
    found: BTreeSet<GapPair>,
}
impl<F> Search<'_, F> {
    fn count<E>(&mut self) -> Result<(), Error<E>> {
        if self.result.rectangle_tests >= self.limits.predicates {
            return Err(Error::Unknown("rectangle predicate limit"));
        }
        self.result.rectangle_tests += 1;
        Ok(())
    }
    fn report<E>(&mut self, pair: GapPair) -> Result<(), Error<E>> {
        if !self.found.contains(&pair) && self.found.len() >= self.limits.output_splits {
            return Err(Error::Unknown("output split limit"));
        }
        self.found.insert(pair);
        Ok(())
    }
}
impl<F, E> Search<'_, F> where F: FnMut(Quartet) -> Result<u8, E> {
    fn ask(&mut self, positions: [usize; 4]) -> Result<u8, Error<E>> {
        if !positions.windows(2).all(|w| w[0] < w[1]) ||
            positions[3] >= self.circle.len() {
            return Err(Error::Invalid("internal sorted position quartet"));
        }
        let labelled = positions.map(|i| self.circle[i]);
        let mut original = labelled;
        original.sort_unstable();
        let mask = if let Some(&mask) = self.result.cache.get(&original) { mask } else {
            if self.result.cache.len() >= self.limits.unique_queries {
                return Err(Error::Unknown("distinct quartet query limit"));
            }
            let mask = (self.oracle)(original).map_err(Error::Oracle)?;
            // Validate before entering the cache; no false NO or partial result.
            remap_support::<E>(labelled,mask)?;
            self.result.cache.insert(original,mask);
            mask
        };
        remap_support(labelled,mask)
    }
    fn visit(&mut self, root: [usize; 4]) -> Result<(), Error<E>> {
        let mut stack = vec![(root,0usize)];
        if stack.len() > self.limits.pending {
            return Err(Error::Unknown("pending rectangle limit"));
        }
        while let Some(([a,b,c,d],depth)) = stack.pop() {
            self.count()?;
            self.result.max_search_depth = self.result.max_search_depth.max(depth);
            if self.ask([a,b,c,d])? & 4 == 0 { continue; }
            let (width,height) = (b-a,d-c);
            if width == 1 && height == 1 {
                self.report([a,c])?;
                continue;
            }
            self.result.positive_internal_nodes += 1;
            let next_depth = depth.checked_add(1).ok_or(Error::Unknown("search depth overflow"))?;
            if stack.len().checked_add(2).ok_or(Error::Unknown("pending count overflow"))? >
                self.limits.pending {
                return Err(Error::Unknown("pending rectangle limit"));
            }
            // Right child is pushed first to retain the OLD left-first trace.
            if width >= height {
                let m = a + width/2;
                stack.push(([m,b,c,d],next_depth));
                stack.push(([a,m,c,d],next_depth));
            } else {
                let m = c + height/2;
                stack.push(([a,b,m,d],next_depth));
                stack.push(([a,b,c,m],next_depth));
            }
        }
        Ok(())
    }
}

/// The same wrap tests, root partition, longer-dimension bisection, bit
/// predicates and original-label cache as the retained reference algorithm.
/// Source/circle/completeness promises are caller obligations. Any failure
/// aborts the ENTIRE recovery; this function never returns a successful prefix.
pub fn recover<E, F>(circle: &[u64], oracle: F, limits: Limits) -> Result<Recovery, Error<E>>
where F: FnMut(Quartet) -> Result<u8, E> {
    let n = circle.len();
    if n < 4 { return Err(Error::Invalid("at least four taxa")); }
    if n > limits.taxa { return Err(Error::Unknown("taxon limit")); }
    let labels: BTreeSet<_> = circle.iter().copied().collect();
    if labels.len() != n { return Err(Error::Invalid("distinct original circle labels")); }
    n.checked_mul(n-3).ok_or(Error::Unknown("candidate count overflow"))?;
    let mut search = Search { circle,oracle,limits,found:BTreeSet::new(),
        result:Recovery { gap_pairs:vec![],cache:BTreeMap::new(),rectangle_tests:0,
            positive_internal_nodes:0,max_search_depth:0 } };
    for i in 1..n-2 {
        search.count()?;
        if search.ask([0,i,i+1,n-1])? & 1 != 0 { search.report([i,n-1])?; }
    }
    let mut intervals = vec![(0,n-1)];
    if intervals.len() > limits.pending { return Err(Error::Unknown("pending interval limit")); }
    while let Some((l,r)) = intervals.pop() {
        if r-l <= 2 { continue; }
        let m = l + (r-l)/2;
        if l < m-1 { search.visit([l,m-1,m,r])?; }
        if m+1 < r { search.visit([m-1,m,m+1,r])?; }
        if intervals.len().checked_add(2).ok_or(Error::Unknown("pending interval overflow"))? >
            limits.pending { return Err(Error::Unknown("pending interval limit")); }
        intervals.push((m,r));
        intervals.push((l,m));
    }
    search.result.gap_pairs = search.found.into_iter().collect();
    Ok(search.result)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn oracle(circle: &[u64], splits: &[GapPair], q: Quartet) -> u8 {
        let mut out = 0;
        for &[i,j] in splits {
            let positions = q.map(|x| circle.iter().position(|y| *y == x).unwrap());
            let shore: Vec<_> = (0..4).filter(|&k| i < positions[k] && positions[k] <= j).collect();
            if shore.len() == 2 {
                out |= pair_bit::<()>(q,[q[shore[0]],q[shore[1]]]).unwrap();
            }
        }
        out
    }
    #[test]
    fn original_label_bits_and_cache_are_not_circle_positions() {
        let circle = [40,10,30,20];
        let mut calls = vec![];
        let r = recover(&circle, |q| { calls.push(q);Ok::<_,()>(oracle(&circle,&[[0,2]],q)) },
            Limits::default()).unwrap();
        assert_eq!(r.gap_pairs,vec![[0,2]]);
        assert_eq!(calls,vec![[10,20,30,40]]);
        assert_eq!(r.cache.len(),1);
        assert_eq!(r.rectangle_tests,2);
    }
    #[test]
    fn limits_and_missing_answers_abort_instead_of_returning_a_prefix() {
        let circle = [0,1,2,3,4];
        let mut calls = 0;
        let e = recover(&circle, |_| { calls += 1;Ok::<_,()>(1) },
            Limits { unique_queries:0,..Limits::default() });
        assert_eq!(e,Err(Error::Unknown("distinct quartet query limit")));
        assert_eq!(calls,0);
        assert_eq!(recover(&circle, |_| Err::<u8,_>("missing"),
            Limits::default()),Err(Error::Oracle("missing")));
        assert_eq!(recover(&[0,0,2,3], |_| Ok::<_,()>(1),Limits::default()),
            Err(Error::Invalid("distinct original circle labels")));
        assert!(matches!(recover(&[0,1,2,3], |_| Ok::<_,()>(2),Limits::default()),
            Err(Error::Invalid("support crosses the supplied circle"))));
        assert!(matches!(recover(&[0,1,2,3], |_| Ok::<_,()>(0),Limits::default()),
            Err(Error::Invalid("nonempty resolved support mask"))));
    }
    #[test]
    fn retained_reference_and_new_rust_match_on_fixed_interface_cases() {
        // New port/interface controls, NOT replay of any old source/graph/main
        // experiment. The retained Python module is byte-identical; no graph
        // helper or archived test runner is invoked.
        let mut cases = Vec::new();
        for n in [4usize,5,7,8] {
            let circle: Vec<_> = (0..n).map(|i| 17+11*((3*i+1)%n) as u64).collect();
            // Use a bijection for every n (3 is not coprime to all sizes).
            let circle: Vec<_> = if circle.iter().collect::<BTreeSet<_>>().len()==n {
                circle
            } else { (0..n).rev().map(|i| 17+11*i as u64).collect() };
            let chain: Vec<_> = (2..n-1).map(|j| [0,j]).collect();
            let dense: Vec<_> = (0..n).flat_map(|i|(i+2..n).map(move |j|[i,j]))
                .filter(|x| *x!=[0,n-1]).collect();
            cases.push((circle.clone(),chain));
            cases.push((circle,dense));
        }
        let request: Vec<_> = cases.iter().map(|(circle,splits)|
            serde_json::json!({"circle":circle,"splits":splits})).collect();
        let program = r#"
import json,sys
sys.path.insert(0,sys.argv[1])
from sparse_quartet import recover,split_support_oracle
out=[]
for case in json.load(sys.stdin):
    n=len(case["circle"])
    reference=recover(n,split_support_oracle(n,map(tuple,case["splits"])))
    out.append({"splits":sorted(reference.splits),"queries":reference.oracle_calls,
      "tests":reference.rectangle_tests,"positive":reference.positive_internal_nodes,
      "depth":reference.max_search_depth})
json.dump(out,sys.stdout)
"#;
        let reference = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/exact-query-reference");
        let mut child = std::process::Command::new("python3").arg("-B").arg("-c")
            .arg(program).arg(reference).stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped())
            .env("PYTHONDONTWRITEBYTECODE","1").spawn().expect("Python3 reference-test dependency");
        use std::io::Write;
        child.stdin.take().unwrap().write_all(serde_json::to_string(&request).unwrap().as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
        let expected: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        for ((circle,splits),e) in cases.iter().zip(expected.as_array().unwrap()) {
            let r = recover(circle,|q| Ok::<_,()>(oracle(circle,splits,q)),Limits::default()).unwrap();
            assert_eq!(serde_json::json!(r.gap_pairs),e["splits"]);
            assert_eq!(serde_json::json!(r.cache.len()),e["queries"]);
            assert_eq!(serde_json::json!(r.rectangle_tests),e["tests"]);
            assert_eq!(serde_json::json!(r.positive_internal_nodes),e["positive"]);
            assert_eq!(serde_json::json!(r.max_search_depth),e["depth"]);
        }
    }
}

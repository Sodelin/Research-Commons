//! Concrete first/last physical-tip retention for OLD CB-NANUQ-004.
//! A contour is supplied, not inferred from a graph. No tree restriction,
//! displayed-quartet equality, probability law or source admission is claimed.
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub tips: usize,
    pub render_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { tips: 256, render_bytes: 262144 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Interleaved { taxon: u32, original_position: usize },
    Limit { kind: &'static str, cap: usize },
}
/// Owns the SAME original labels, cut, dense label table and returned IDs.
/// Private fields prevent replacing the input behind an emitted certificate.
#[derive(Clone, Debug)]
pub struct Retention {
    original: Vec<u32>,
    cut: usize,
    global_taxa: Vec<u32>,
    rotated_taxa: Vec<usize>,
    original_positions: Vec<usize>,
    kept_rotated: Vec<usize>,
    kept_original: Vec<usize>,
}
impl Retention {
    /// O(n log k), one actual occurrence block per taxon in cyclic order.
    /// Empty/single-label contours are useful core cases, not NANUQ admission.
    pub fn new(labels: &[u32], limits: Limits) -> Result<Self, Error> {
        if labels.len() > limits.tips {
            return Err(Error::Limit { kind: "tips", cap: limits.tips });
        }
        let n = labels.len();
        let cut = (0..n).find(|&i| labels[i] != labels[if i == 0 { n - 1 } else { i - 1 }])
            .unwrap_or(0);
        let original_positions: Vec<usize> = (0..n)
            .map(|i| if i < n - cut { cut + i } else { i - (n - cut) })
            .collect();
        let mut closed = BTreeSet::new();
        let mut previous = None;
        let mut extrema: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
        for (i, &original_position) in original_positions.iter().enumerate() {
            let label = labels[original_position];
            if previous != Some(label) {
                if closed.contains(&label) {
                    return Err(Error::Interleaved { taxon: label, original_position });
                }
                if let Some(old) = previous { closed.insert(old); }
                previous = Some(label);
            }
            extrema.entry(label).and_modify(|v| v.1 = i).or_insert((i, i));
        }
        let global_taxa: Vec<u32> = extrema.keys().copied().collect();
        let dense: BTreeMap<u32, usize> = global_taxa.iter().copied()
            .enumerate().map(|(i, t)| (t, i)).collect();
        let rotated_taxa = original_positions.iter().map(|&i| dense[&labels[i]]).collect();
        let kept_rotated: Vec<usize> = original_positions.iter().enumerate()
            .filter_map(|(i, &p)| {
                let &(first, last) = &extrema[&labels[p]];
                (i == first || i == last).then_some(i)
            }).collect();
        let kept_original = kept_rotated.iter().map(|&i| original_positions[i]).collect();
        Ok(Self { original: labels.to_vec(), cut, global_taxa, rotated_taxa,
            original_positions, kept_rotated, kept_original })
    }
    pub fn original_labels(&self) -> &[u32] { &self.original }
    pub fn cut(&self) -> usize { self.cut }
    pub fn taxon_table(&self) -> &[u32] { &self.global_taxa }
    pub fn retained_original_positions(&self) -> &[usize] { &self.kept_original }
    pub fn retained_contour_positions(&self) -> &[usize] { &self.kept_rotated }
    /// The literal input, relabelling, permutation, contiguity and ENTIRE
    /// returned set are rechecked in Lean. This is output, not proof acceptance.
    pub fn lean_certificate(&self, limits: Limits) -> Result<String, Error> {
        if self.original.len() > limits.tips {
            return Err(Error::Limit { kind: "tips", cap: limits.tips });
        }
        let n = self.original.len();
        let k = self.global_taxa.len();
        let namespace = format!("ResearchCommons.Generated.Contiguous.N{n}C{}{}",
            self.cut, self.original.iter().map(|t| format!("X{t}")).collect::<String>());
        let array = |values: Vec<String>, domain: usize| {
            if domain == 0 { "fun i => Fin.elim0 i".to_owned() }
            else { format!("![{}]", values.join(", ")) }
        };
        let nat_array = |xs: &[u32]| array(xs.iter().map(u32::to_string).collect(), xs.len());
        let fin_array = |xs: &[usize]| array(xs.iter().map(usize::to_string).collect(), xs.len());
        let set = |xs: &[usize]| if xs.is_empty() { "∅".to_owned() }
            else { format!("{{{}}}", xs.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")) };
        let original = nat_array(&self.original);
        let names = nat_array(&self.global_taxa);
        let positions = fin_array(&self.original_positions);
        let taxa = fin_array(&self.rotated_taxa);
        let kept = set(&self.kept_rotated);
        let returned = set(&self.kept_original);
        let source = format!(r#"import ResearchCommons.NANUQ.ContiguousCopies

namespace {namespace}
open ResearchCommons.NANUQ.ContiguousCopies
def originalLabels : Fin {n} → Nat := {original}
def globalTaxa : Fin {k} → Nat := {names}
def originalPosition : Fin {n} → Fin {n} := {positions}
def taxon : Fin {n} → Fin {k} := {taxa}
def kept : Finset (Fin {n}) := {kept}
def keptOriginal : Finset (Fin {n}) := {returned}
theorem actual_names : Function.Injective globalTaxa := by decide
theorem actual_original_positions : Function.Bijective originalPosition := by decide
theorem same_original_label (i : Fin {n}) :
    globalTaxa (taxon i) = originalLabels (originalPosition i) := by
  revert i
  decide
theorem actual_contiguous : Contiguous taxon := by
  unfold Contiguous
  decide
theorem actual_extremes (i : Fin {n}) :
    i ∈ kept ↔ Extreme taxon i := by
  revert i
  unfold Extreme First Last
  decide
theorem actual_returned_positions :
    kept.image originalPosition = keptOriginal := by decide
theorem actual_bound : keptOriginal.card ≤ 2 * {k} := by decide
theorem uniform_extreme_bound :
    Nat.card {{i : Fin {n} // Extreme taxon i}} ≤ 2 * {k} := by
  simpa only [Fintype.card_fin] using extreme_card_le_two taxon
theorem every_original_taxon_retained (i : Fin {n}) :
    ∃ e ∈ kept, taxon e = taxon i := by
  obtain ⟨f, g, hf, hg, hfirst, hlast, hfi, hig⟩ := extreme_bounds taxon i
  exact ⟨f, (actual_extremes f).mpr (Or.inl hfirst), hf⟩
theorem same_interval_side (l r i : Fin {n})
    (h : ∃ a b, InInterval l r a ∧ InInterval l r b ∧ taxon a ≠ taxon b) :
    ∃ e ∈ kept, taxon e = taxon i ∧
      (InInterval l r e ↔ InInterval l r i) := by
  obtain ⟨e, he, ht, hs⟩ := same_interval_side_extreme taxon actual_contiguous l r h i
  exact ⟨e, (actual_extremes e).mpr he, ht, hs⟩
theorem complete_supplied_cut_quartets (l r : Fin {n}) (a b c d : Fin {k})
    (hab : a ≠ b) :
    CutQuartet taxon (fun i => i ∈ kept) l r a b c d ↔
      CutQuartet taxon (fun _ => True) l r a b c d := by
  simpa only [CutQuartet, actual_extremes] using
    cut_quartet_extremes_iff taxon actual_contiguous l r a b c d hab
theorem complete_supplied_cut_splits (l r : Fin {n}) (left : Fin {k} → Prop)
    (h : ∃ a b, left a ∧ left b ∧ a ≠ b) :
    CutSplit taxon (fun i => i ∈ kept) l r left ↔
      CutSplit taxon (fun _ => True) l r left := by
  simpa only [CutSplit, actual_extremes] using
    cut_split_extremes_iff taxon actual_contiguous l r left h
end {namespace}
"#);
        if source.len() > limits.render_bytes {
            return Err(Error::Limit { kind: "render_bytes", cap: limits.render_bytes });
        }
        Ok(source)
    }
}
pub fn example_certificate(wrapped: bool) -> Result<String, Error> {
    let labels: &[u32] = if wrapped {
        &[7, 7, 40, 40, 90, 90, 90, 120, 7]
    } else { &[7, 7, 40, 90, 90, 90, 120, 120] };
    Retention::new(labels, Limits::default())?.lean_certificate(Limits::default())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_extremes_keep_singletons_and_original_ids() {
        let r = Retention::new(&[7,7,7,40,90,90,90,120,120], Limits::default()).unwrap();
        assert_eq!(r.cut(), 0);
        assert_eq!(r.taxon_table(), &[7,40,90,120]);
        assert_eq!(r.retained_original_positions(), &[0,2,3,4,6,7,8]);
        assert_eq!(r.original_labels(), &[7,7,7,40,90,90,90,120,120]);
    }
    #[test]
    fn cyclic_wrap_is_not_interleaving_or_reindexing_original_tips() {
        let r = Retention::new(&[7,7,40,40,90,90,90,120,7], Limits::default()).unwrap();
        assert_eq!(r.cut(), 2);
        assert_eq!(r.retained_original_positions(), &[2,3,4,6,7,8,1]);
        assert!(r.lean_certificate(Limits::default()).unwrap().contains("same_original_label"));
        assert_eq!(Retention::new(&[7,40,7,90], Limits::default()).unwrap_err(),
            Error::Interleaved { taxon: 7, original_position: 2 });
    }
    #[test]
    fn empty_singleton_sparse_labels_and_limits_remain_explicit() {
        let l = Limits::default();
        assert!(Retention::new(&[], l).unwrap().retained_original_positions().is_empty());
        let one = Retention::new(&[u32::MAX], l).unwrap();
        assert_eq!(one.retained_original_positions(), &[0]);
        assert_eq!(Retention::new(&[1,2], Limits { tips: 1, ..l }).unwrap_err(),
            Error::Limit { kind: "tips", cap: 1 });
        assert_eq!(one.lean_certificate(Limits { render_bytes: 1, ..l }).unwrap_err(),
            Error::Limit { kind: "render_bytes", cap: 1 });
        assert_ne!(example_certificate(false).unwrap(), example_certificate(true).unwrap());
    }
    #[test]
    fn all_small_contours_match_independent_cyclic_block_and_extreme_oracles() {
        for n in 0u32..=7 {
            for mut word in 0usize..3usize.pow(n) {
                let labels: Vec<u32> = (0..n).map(|_| {
                    let x = (word % 3) as u32; word /= 3; x
                }).collect();
                let distinct: BTreeSet<u32> = labels.iter().copied().collect();
                let valid = distinct.iter().all(|&t| {
                    let starts = (0..labels.len()).filter(|&i| labels[i]==t &&
                        labels[if i==0 { labels.len()-1 } else { i-1 }] != t).count();
                    starts <= 1
                });
                let actual = Retention::new(&labels, Limits::default());
                assert_eq!(actual.is_ok(), valid, "labels={labels:?}");
                if let Ok(r) = actual {
                    let expected: Vec<usize> = (0..labels.len()).filter(|&i| {
                        let t = labels[r.original_positions[i]];
                        let matches: Vec<usize> = (0..labels.len())
                            .filter(|&j| labels[r.original_positions[j]]==t).collect();
                        matches.first()==Some(&i) || matches.last()==Some(&i)
                    }).map(|i| r.original_positions[i]).collect();
                    assert_eq!(r.retained_original_positions(), expected);
                    assert!(expected.len() <= 2 * distinct.len());
                    assert_eq!(expected.iter().map(|&i| labels[i]).collect::<BTreeSet<_>>(), distinct);
                }
            }
        }
    }
}

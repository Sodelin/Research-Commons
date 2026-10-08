//! Offline sequence construction only. This crate makes no biological prediction.
#![forbid(unsafe_code)]

pub const MAX_INPUT_BYTES: usize = 8 * 1024 * 1024;
pub const MAX_SEQUENCE_LENGTH: usize = 1 << 20;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreError {
    pub status: &'static str,
    pub code: &'static str,
    pub message: String,
}
impl CoreError {
    pub fn invalid(code: &'static str, message: impl Into<String>) -> Self {
        Self { status: "INVALID_INPUT", code, message: message.into() }
    }
    pub fn resource(message: impl Into<String>) -> Self {
        Self { status: "RESOURCE_LIMIT", code: "RESOURCE_LIMIT", message: message.into() }
    }
    fn unsupported(message: impl Into<String>) -> Self {
        Self { status: "UNSUPPORTED", code: "COMPLEX_DELINS", message: message.into() }
    }
}
pub type Result<T> = std::result::Result<T, CoreError>;

#[derive(Clone, Debug)]
pub struct ReferenceWindow {
    pub assembly: String,
    pub chromosome: String,
    pub start0: u64,
    pub sequence: String,
    /// Adjacent right-hand reference bases, authenticated by the calling service.
    pub guard_sequence: String,
}
#[derive(Clone, Debug)]
pub struct Variant {
    pub id: String,
    pub chromosome: String,
    pub pos1: u64,
    pub reference: String,
    pub alternate: String,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhaseKind { Cis, Trans, Unknown, Hypothetical }
impl PhaseKind {
    pub fn as_str(self) -> &'static str {
        match self { Self::Cis => "cis", Self::Trans => "trans", Self::Unknown => "unknown", Self::Hypothetical => "hypothetical" }
    }
    pub fn parse(value: &str) -> Result<Self> {
        match value {
            "cis" => Ok(Self::Cis), "trans" => Ok(Self::Trans),
            "unknown" => Ok(Self::Unknown), "hypothetical" => Ok(Self::Hypothetical),
            _ => Err(CoreError::invalid("PHASE", "unsupported phase kind")),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Phase { pub kind: PhaseKind, pub evidence_present: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceRange { pub start0: u64, pub end0: u64 }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapSegment {
    pub sequence_start: usize,
    pub sequence_end: usize,
    pub reference_start0: Option<u64>,
    pub reference_end0: Option<u64>,
}
#[derive(Clone, Debug)]
pub struct Scenario {
    pub id: &'static str,
    pub sequence: String,
    pub coordinate_map: Vec<MapSegment>,
    pub deleted_reference_ranges: Vec<ReferenceRange>,
    pub cropped_reference_ranges: Vec<ReferenceRange>,
    pub cropped_bases: usize,
    pub cropped_inserted_bases: usize,
    pub counterfactual: bool,
}
#[derive(Clone, Debug)]
pub struct HaplotypeBundle {
    pub assembly: String,
    pub chromosome: String,
    pub window_start0: u64,
    pub sequence_length: usize,
    pub phase: Phase,
    pub scenarios: Vec<Scenario>,
}

fn identifier(s: &str) -> bool {
    !s.is_empty() && s.len() <= 128 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b"_.:-".contains(&b))
}
fn dna(s: &str, allow_n: bool) -> bool {
    s.bytes().all(|b| b"ACGT".contains(&b) || (allow_n && b == b'N'))
}
fn end(start: u64, length: usize) -> Result<u64> {
    start.checked_add(length as u64).ok_or_else(|| CoreError::invalid("COORDINATE", "coordinate overflow"))
}
fn overlaps(a: &ReferenceRange, b: &ReferenceRange) -> bool { a.start0 < b.end0 && b.start0 < a.end0 }

#[derive(Clone, Debug)]
struct Edit { start: usize, stop: usize, keep: usize, insertion: bool, variant: Variant }
fn validate(window: &ReferenceWindow, variants: &[Variant], phase: &Phase, roi: Option<&ReferenceRange>) -> Result<Vec<Edit>> {
    if !matches!(window.assembly.as_str(), "GRCh38" | "GRCh38.p13" | "hg38") {
        return Err(CoreError::invalid("ASSEMBLY", "human GRCh38/GRCh38.p13/hg38 reference required"));
    }
    if !identifier(&window.chromosome) { return Err(CoreError::invalid("CHROMOSOME", "invalid chromosome label")); }
    let length = window.sequence.len();
    if length == 0 || length > MAX_SEQUENCE_LENGTH || window.guard_sequence.len() > MAX_SEQUENCE_LENGTH {
        return Err(CoreError::resource("reference/guard sequence length outside bounded core contract"));
    }
    if !dna(&window.sequence, true) || !dna(&window.guard_sequence, true) {
        return Err(CoreError::invalid("REFERENCE_SEQUENCE", "reference and guard must be uppercase ACGTN"));
    }
    let window_end = end(window.start0, length)?;
    end(window_end, window.guard_sequence.len())?;
    if let Some(r) = roi {
        if r.start0 >= r.end0 || r.start0 < window.start0 || r.end0 > window_end {
            return Err(CoreError::invalid("ROI", "ROI must be nonempty and inside the reference window"));
        }
    }
    if matches!(phase.kind,PhaseKind::Cis|PhaseKind::Trans) && !phase.evidence_present {
        return Err(CoreError::invalid("PHASE_EVIDENCE", "cis/trans requires explicit phase evidence"));
    }
    if variants.len() != 2 { return Err(CoreError::invalid("VARIANT_COUNT", "exactly two variants required")); }
    if variants[0].id == variants[1].id { return Err(CoreError::invalid("VARIANT_ID", "duplicate variant ID")); }
    let mut edits = Vec::new();
    for v in variants {
        if !identifier(&v.id) { return Err(CoreError::invalid("VARIANT_ID", "invalid variant ID")); }
        if v.chromosome != window.chromosome { return Err(CoreError::invalid("CHROMOSOME", "variant chromosome differs from reference")); }
        if v.reference.len() > MAX_SEQUENCE_LENGTH || v.alternate.len() > MAX_SEQUENCE_LENGTH {
            return Err(CoreError::resource("allele length exceeds bounded core contract"));
        }
        if v.reference.is_empty() || v.alternate.is_empty() || !dna(&v.reference, false) || !dna(&v.alternate, false) {
            return Err(CoreError::invalid("ALLELE", "anchored nonempty uppercase ACGT alleles required"));
        }
        if v.reference == v.alternate { return Err(CoreError::invalid("ALLELE", "REF and ALT must differ")); }
        let start0 = v.pos1.checked_sub(1).ok_or_else(|| CoreError::invalid("COORDINATE", "VCF position must be at least one"))?;
        let stop0 = end(start0, v.reference.len())?;
        if start0 < window.start0 || stop0 > window_end { return Err(CoreError::invalid("VARIANT_RANGE", "full REF span must lie in reference window")); }
        let start = (start0 - window.start0) as usize;
        let stop = (stop0 - window.start0) as usize;
        if window.sequence.as_bytes()[start..stop] != *v.reference.as_bytes() {
            return Err(CoreError::invalid("REFERENCE_MISMATCH", "full REF allele does not match supplied reference"));
        }
        let (keep, insertion) = if v.reference.len() == v.alternate.len() {
            (v.reference.len(), false)
        } else if v.alternate.starts_with(&v.reference) {
            (v.reference.len(), true)
        } else if v.reference.starts_with(&v.alternate) {
            (v.alternate.len(), false)
        } else { return Err(CoreError::unsupported("only equal-length substitutions and prefix-anchored insertion/deletion are supported")); };
        edits.push(Edit { start, stop, keep, insertion, variant: v.clone() });
    }
    if edits[0].start < edits[1].stop && edits[1].start < edits[0].stop {
        return Err(CoreError::invalid("OVERLAPPING_VARIANTS", "overlapping REF spans or duplicate positions are not admitted"));
    }
    Ok(edits)
}
fn append_piece(sequence: &mut String, maps: &mut Vec<MapSegment>, text: &str, reference_start0: Option<u64>) {
    if text.is_empty() { return; }
    let start = sequence.len(); sequence.push_str(text);
    let reference_end0 = reference_start0.map(|r| r + text.len() as u64);
    if let Some(last) = maps.last_mut() {
        if last.sequence_end == start && last.reference_end0 == reference_start0 && last.reference_start0.is_some() == reference_start0.is_some() {
            last.sequence_end = sequence.len(); last.reference_end0 = reference_end0; return;
        }
    }
    maps.push(MapSegment { sequence_start: start, sequence_end: sequence.len(), reference_start0, reference_end0 });
}
fn construct(window: &ReferenceWindow, selected: &[&Edit], id: &'static str, phase: &Phase, roi: Option<&ReferenceRange>) -> Result<Scenario> {
    let full = format!("{}{}", window.sequence, window.guard_sequence);
    let mut edits = selected.to_vec(); edits.sort_by_key(|e| e.start);
    let mut sequence = String::new(); let mut maps = Vec::new(); let mut deleted = Vec::new(); let mut cursor = 0;
    let mut edited_ranges = Vec::new();
    for e in edits {
        append_piece(&mut sequence, &mut maps, &full[cursor..e.start], Some(window.start0 + cursor as u64));
        let edit_output_start = sequence.len();
        append_piece(&mut sequence, &mut maps, &e.variant.alternate[..e.keep], Some(window.start0 + e.start as u64));
        if e.insertion {
            append_piece(&mut sequence, &mut maps, &e.variant.alternate[e.keep..], None);
        } else if e.keep < e.variant.reference.len() {
            deleted.push(ReferenceRange { start0: window.start0 + (e.start + e.keep) as u64, end0: window.start0 + e.stop as u64 });
        }
        edited_ranges.push((edit_output_start, sequence.len())); cursor = e.stop;
    }
    append_piece(&mut sequence, &mut maps, &full[cursor..], Some(window.start0 + cursor as u64));
    let length = window.sequence.len();
    if sequence.len() < length { return Err(CoreError::invalid("INSUFFICIENT_GUARD", "deletion requires enough authenticated right-hand guard bases")); }
    if edited_ranges.iter().any(|&(a,b)| a >= length || b > length) {
        return Err(CoreError::invalid("EDIT_CROPPED", "fixed-length crop would lose an edited allele"));
    }
    let cropped_bases = sequence.len() - length;
    let mut cropped_reference_ranges = Vec::new(); let mut cropped_inserted_bases = 0;
    for m in &maps {
        if m.sequence_end > length {
            let first = m.sequence_start.max(length);
            if let Some(r) = m.reference_start0 {
                let range = ReferenceRange { start0: r + (first - m.sequence_start) as u64, end0: m.reference_end0.unwrap() };
                if roi.is_some_and(|roi| overlaps(roi, &range)) {
                    return Err(CoreError::invalid("ROI_CROPPED", "fixed-length crop would lose retained ROI reference bases"));
                }
                cropped_reference_ranges.push(range);
            } else { cropped_inserted_bases += m.sequence_end - first; }
        }
    }
    maps.retain(|m| m.sequence_start < length);
    for m in &mut maps {
        if m.sequence_end > length {
            m.sequence_end = length;
            m.reference_end0 = m.reference_start0.map(|r| r + (length - m.sequence_start) as u64);
        }
    }
    sequence.truncate(length);
    Ok(Scenario { id, sequence, coordinate_map: maps, deleted_reference_ranges: deleted, cropped_reference_ranges, cropped_bases, cropped_inserted_bases,
        counterfactual: id == "AB" && phase.kind != PhaseKind::Cis })
}

/// Input order declares A and B; all edits use original reference coordinates.
pub fn build_haplotypes(window: &ReferenceWindow, variants: &[Variant], phase: &Phase, roi: Option<ReferenceRange>) -> Result<HaplotypeBundle> {
    let edits = validate(window, variants, phase, roi.as_ref())?;
    let mut scenarios = Vec::new();
    for (id, selected) in [("REF", vec![]), ("A", vec![&edits[0]]), ("B", vec![&edits[1]]), ("AB", vec![&edits[0], &edits[1]])] {
        scenarios.push(construct(window, &selected, id, phase, roi.as_ref())?);
    }
    Ok(HaplotypeBundle { assembly: window.assembly.clone(), chromosome: window.chromosome.clone(), window_start0: window.start0,
        sequence_length: window.sequence.len(), phase: phase.clone(), scenarios })
}

#[derive(Clone, Debug)]
pub struct Request { pub window: ReferenceWindow, pub variants: Vec<Variant>, pub phase: Phase, pub roi: Option<ReferenceRange> }
fn coordinate(value: &str) -> Result<u64> {
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) { return Err(CoreError::invalid("PROTOCOL", "unsigned decimal coordinate required")); }
    value.parse().map_err(|_| CoreError::invalid("COORDINATE", "coordinate overflow"))
}
/// Versioned flat TSV bridge. The caller authenticates reference and annotation sources.
pub fn parse_request(input: &str) -> Result<Request> {
    if input.len() > MAX_INPUT_BYTES { return Err(CoreError::resource("stdin request exceeds 8MiB")); }
    let mut lines = input.lines();
    if lines.next() != Some("molecular-haplotype-v1") { return Err(CoreError::invalid("PROTOCOL", "expected molecular-haplotype-v1 header")); }
    let mut window = None; let mut phase = None; let mut variants = Vec::new(); let mut roi = None;
    for line in lines {
        let f: Vec<&str> = line.split('\t').collect();
        match f.as_slice() {
            ["window", assembly, chromosome, start, sequence, guard] if window.is_none() => {
                window = Some(ReferenceWindow { assembly: (*assembly).into(), chromosome: (*chromosome).into(), start0: coordinate(start)?, sequence: (*sequence).into(), guard_sequence: (*guard).into() });
            }
            ["phase", kind, evidence] if phase.is_none() => {
                let evidence_present = match *evidence { "true" => true, "false" => false, _ => return Err(CoreError::invalid("PROTOCOL", "phase evidence must be true or false")) };
                phase = Some(Phase { kind: PhaseKind::parse(kind)?, evidence_present });
            }
            ["variant", id, chromosome, pos1, reference, alternate] if variants.len() < 2 => {
                variants.push(Variant { id: (*id).into(), chromosome: (*chromosome).into(), pos1: coordinate(pos1)?, reference: (*reference).into(), alternate: (*alternate).into() });
            }
            ["roi", start, stop] if roi.is_none() => roi = Some(ReferenceRange { start0: coordinate(start)?, end0: coordinate(stop)? }),
            _ => return Err(CoreError::invalid("PROTOCOL", "unknown, duplicate, or malformed protocol field")),
        }
    }
    Ok(Request { window: window.ok_or_else(|| CoreError::invalid("PROTOCOL", "missing reference window"))?,
        phase: phase.ok_or_else(|| CoreError::invalid("PROTOCOL", "missing phase"))?, variants, roi })
}
pub fn json_string(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""), '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"), '\r' => out.push_str("\\r"), '\t' => out.push_str("\\t"),
            c if (c as u32) < 32 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"'); out
}
fn ranges_json(ranges: &[ReferenceRange]) -> String {
    format!("[{}]", ranges.iter().map(|r| format!("{{\"start0\":{},\"end0\":{}}}",r.start0,r.end0)).collect::<Vec<_>>().join(","))
}
fn optional_coordinate(value: Option<u64>) -> String { value.map_or_else(|| "null".into(), |v| v.to_string()) }
pub fn bundle_json(bundle: &HaplotypeBundle) -> String {
    let scenarios = bundle.scenarios.iter().map(|s| {
        let maps = s.coordinate_map.iter().map(|m| format!("{{\"sequence_start\":{},\"sequence_end\":{},\"reference_start0\":{},\"reference_end0\":{}}}", m.sequence_start,m.sequence_end,optional_coordinate(m.reference_start0),optional_coordinate(m.reference_end0))).collect::<Vec<_>>().join(",");
        format!("{}:{{\"sequence\":{},\"coordinate_map\":[{}],\"deleted_reference_ranges\":{},\"cropped_reference_ranges\":{},\"cropped_bases\":{},\"cropped_inserted_bases\":{},\"counterfactual\":{}}}", json_string(s.id),json_string(&s.sequence),maps,ranges_json(&s.deleted_reference_ranges),ranges_json(&s.cropped_reference_ranges),s.cropped_bases,s.cropped_inserted_bases,s.counterfactual)
    }).collect::<Vec<_>>().join(",");
    format!("{{\"schema\":\"molecular-haplotype-result-v1\",\"status\":\"SUCCESS\",\"assembly\":{},\"chromosome\":{},\"window_start0\":{},\"sequence_length\":{},\"coordinate_policy\":\"fixed_left_edit_guard_crop_first_L\",\"phase\":{{\"kind\":{},\"evidence_present\":{}}},\"scenarios\":{{{}}}}}",json_string(&bundle.assembly),json_string(&bundle.chromosome),bundle.window_start0,bundle.sequence_length,json_string(bundle.phase.kind.as_str()),bundle.phase.evidence_present,scenarios)
}
pub fn error_json(error: &CoreError) -> String {
    format!("{{\"schema\":\"molecular-haplotype-result-v1\",\"status\":{},\"code\":{},\"message\":{}}}", json_string(error.status),json_string(error.code),json_string(&error.message))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn window() -> ReferenceWindow { ReferenceWindow { assembly:"hg38".into(), chromosome:"chr1".into(),start0:0,sequence:"ACGTACGT".into(),guard_sequence:"ACGT".into() } }
    fn v(id:&str,pos1:u64,r:&str,a:&str) -> Variant { Variant { id:id.into(),chromosome:"chr1".into(),pos1,reference:r.into(),alternate:a.into() } }
    fn phase() -> Phase { Phase { kind:PhaseKind::Cis,evidence_present:true } }
    fn run(vs:&[Variant]) -> Result<HaplotypeBundle> { build_haplotypes(&window(),vs,&phase(),None) }
    #[test] fn substitutions_use_original_coordinates() {
        let b=run(&[v("a",1,"A","T"),v("b",8,"T","C")]).unwrap();
        assert_eq!(b.scenarios.iter().map(|s|s.sequence.as_str()).collect::<Vec<_>>(),vec!["ACGTACGT","TCGTACGT","ACGTACGC","TCGTACGC"]);
        assert_eq!(b.scenarios[3].coordinate_map,vec![MapSegment{sequence_start:0,sequence_end:8,reference_start0:Some(0),reference_end0:Some(8)}]);
    }
    #[test] fn insertion_then_downstream_edit_and_map() {
        let b=run(&[v("a",2,"C","CAA"),v("b",5,"A","T")]).unwrap();
        assert_eq!(b.scenarios[3].sequence,"ACAAGTTC");
        assert!(b.scenarios[3].coordinate_map.iter().any(|m|m.sequence_start==2&&m.sequence_end==4&&m.reference_start0.is_none()));
        assert_eq!(b.scenarios[3].cropped_bases,6);
    }
    #[test] fn deletion_uses_guard_and_records_deleted_reference() {
        let b=run(&[v("a",2,"CGT","C"),v("b",6,"C","T")]).unwrap();
        assert_eq!(b.scenarios[3].sequence,"ACATGTAC");
        assert_eq!(b.scenarios[3].deleted_reference_ranges,vec![ReferenceRange{start0:2,end0:4}]);
        assert_eq!(b.scenarios[3].coordinate_map.last().unwrap().reference_end0,Some(10));
    }
    #[test] fn swapping_input_only_swaps_a_and_b() {
        let a=v("a",2,"C","CAA");let b=v("b",5,"A","T");
        let x=run(&[a.clone(),b.clone()]).unwrap();let y=run(&[b,a]).unwrap();
        assert_eq!(x.scenarios[3].sequence,y.scenarios[3].sequence);
        assert_eq!(x.scenarios[1].sequence,y.scenarios[2].sequence);
    }
    #[test] fn combined_indels_can_need_more_guard_than_each_single() {
        let mut w=window();w.guard_sequence="A".into();
        assert_eq!(build_haplotypes(&w,&[v("a",1,"AC","A"),v("b",5,"AC","A")],&phase(),None).unwrap_err().code,"INSUFFICIENT_GUARD");
    }
    #[test] fn phase_cis_requires_evidence_and_other_ab_is_counterfactual() {
        let vs=[v("a",1,"A","T"),v("b",5,"A","T")];
        assert_eq!(build_haplotypes(&window(),&vs,&Phase{kind:PhaseKind::Cis,evidence_present:false},None).unwrap_err().code,"PHASE_EVIDENCE");
        for kind in [PhaseKind::Trans,PhaseKind::Unknown,PhaseKind::Hypothetical] {
            let b=build_haplotypes(&window(),&vs,&Phase{kind,evidence_present:kind==PhaseKind::Trans},None).unwrap();
            assert!(b.scenarios[3].counterfactual);assert!(!b.scenarios[1].counterfactual);
        }
    }
    #[test] fn full_span_ref_check_and_position_one() {
        assert!(run(&[v("a",1,"AC","TT"),v("b",5,"A","T")]).is_ok());
        assert_eq!(run(&[v("a",1,"AT","TT"),v("b",5,"A","T")]).unwrap_err().code,"REFERENCE_MISMATCH");
        assert_eq!(run(&[v("a",0,"A","T"),v("b",5,"A","T")]).unwrap_err().code,"COORDINATE");
        assert_eq!(run(&[v("a",8,"TA","T"),v("b",5,"A","T")]).unwrap_err().code,"VARIANT_RANGE");
    }
    #[test] fn overlap_and_duplicate_identity_are_refused() {
        assert_eq!(run(&[v("a",2,"CG","CC"),v("b",3,"G","A")]).unwrap_err().code,"OVERLAPPING_VARIANTS");
        assert_eq!(run(&[v("a",1,"A","T"),v("a",5,"A","T")]).unwrap_err().code,"VARIANT_ID");
        assert_eq!(run(&[v("a",1,"A","T"),v("b",1,"A","G")]).unwrap_err().code,"OVERLAPPING_VARIANTS");
    }
    #[test] fn wrong_assembly_chromosome_or_allele_are_refused() {
        let vs=[v("a",1,"A","T"),v("b",5,"A","T")];let mut w=window();w.assembly="hg19".into();
        assert_eq!(build_haplotypes(&w,&vs,&phase(),None).unwrap_err().code,"ASSEMBLY");
        let mut vs2=vs.clone();vs2[0].chromosome="chr2".into();assert_eq!(run(&vs2).unwrap_err().code,"CHROMOSOME");
        for allele in ["","N","a","A\tT"] { assert_eq!(run(&[v("a",1,"A",allele),vs[1].clone()]).unwrap_err().code,"ALLELE"); }
    }
    #[test] fn complex_delins_refused_without_guessed_alignment() {
        assert_eq!(run(&[v("a",2,"CG","CAT"),v("b",6,"C","A")]).unwrap_err().status,"UNSUPPORTED");
    }
    #[test] fn lost_edit_or_roi_is_refused() {
        assert_eq!(run(&[v("a",2,"C","CAA"),v("b",8,"T","C")]).unwrap_err().code,"EDIT_CROPPED");
        assert_eq!(build_haplotypes(&window(),&[v("a",2,"C","CAA"),v("b",5,"A","T")],&phase(),Some(ReferenceRange{start0:6,end0:8})).unwrap_err().code,"ROI_CROPPED");
    }
    #[test] fn negative_or_overflowed_reference_range_cannot_wrap() {
        let mut w=window();w.start0=u64::MAX;
        assert_eq!(build_haplotypes(&w,&[v("a",1,"A","T"),v("b",5,"A","T")],&phase(),None).unwrap_err().code,"COORDINATE");
    }
    #[test] fn reference_n_allowed_but_cannot_match_a_variant_allele() {
        let mut w=window();w.sequence="NCGTACGT".into();
        assert_eq!(build_haplotypes(&w,&[v("a",1,"A","T"),v("b",5,"A","T")],&phase(),None).unwrap_err().code,"REFERENCE_MISMATCH");
    }
    #[test] fn map_tiles_fixed_output_and_reference_gaps_are_deletions() {
        let b=run(&[v("a",2,"CGT","C"),v("b",6,"C","CAA")]).unwrap();
        for s in b.scenarios { let mut cursor=0;for m in s.coordinate_map {assert_eq!(m.sequence_start,cursor);assert!(m.sequence_end>cursor);if let (Some(a),Some(z))=(m.reference_start0,m.reference_end0){assert_eq!(z-a,(m.sequence_end-cursor) as u64);}cursor=m.sequence_end;}assert_eq!(cursor,8); }
    }
    #[test] fn protocol_rejects_duplicates_and_bad_version() {
        let s="molecular-haplotype-v1\nwindow\thg38\tchr1\t0\tACGTACGT\tACGT\nphase\tcis\ttrue\nvariant\ta\tchr1\t1\tA\tT\nvariant\tb\tchr1\t5\tA\tT\n";
        let r=parse_request(s).unwrap();assert_eq!(r.variants.len(),2);
        assert!(parse_request(&format!("{s}phase\tcis\ttrue\n")).is_err());
        assert!(parse_request(&s.replacen("molecular-haplotype-v1","bad",1)).is_err());
        assert!(parse_request(&s.replace("\ttrue","\t1")).is_err());
    }
    #[test] fn json_escapes_controls_quote_slash_and_unicode() {
        assert_eq!(json_string("\"\\\n\r\t\0λ"),"\"\\\"\\\\\\n\\r\\t\\u0000λ\"");
    }
    #[test] fn nonzero_window_origin_and_adjacent_spans_are_valid() {
        let mut w=window();w.start0=100;
        let b=build_haplotypes(&w,&[v("a",101,"AC","TT"),v("b",103,"G","A")],&phase(),Some(ReferenceRange{start0:100,end0:104})).unwrap();
        assert_eq!(b.scenarios[3].sequence,"TTATACGT");
        assert_eq!(b.scenarios[3].coordinate_map[0].reference_start0,Some(100));
    }
    #[test] fn biological_deletion_of_roi_is_not_silently_classified_as_crop() {
        let b=build_haplotypes(&window(),&[v("a",2,"CGT","C"),v("b",6,"C","T")],&phase(),Some(ReferenceRange{start0:2,end0:4})).unwrap();
        assert_eq!(b.scenarios[3].deleted_reference_ranges,vec![ReferenceRange{start0:2,end0:4}]);
        assert!(b.scenarios[3].cropped_reference_ranges.iter().all(|r|!overlaps(r,&ReferenceRange{start0:2,end0:4})));
    }
}

//! Actual retained affine solver -> literal, independently checked Lean source.
//! This certifies the supplied matrix. Source admission and chart/physical
//! refinement are distinct from a particular checked matrix certificate.
use parity_solver::{affine::{self,Decision,Row},q,Rational};

#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error { Invalid(&'static str), Unknown, SourceLimit }
fn rational(x:&Rational)->String { format!("({} / {} : ℚ)",x.numer(),x.denom()) }
fn vector(items:Vec<String>)->String {
    if items.is_empty() { "Fin.elim0".into() } else {format!("![{}]",items.join(", "))}
}
fn row_literal(row:&Row)->String {
    format!("⟨{}, {}, {}⟩",vector(row.coefficients.iter().map(rational).collect()),
        rational(&row.bound),row.strict)
}
/// Own the complete ordered matrix through solve/render; duplicate positions
/// remain present in both rows and external exclusion multipliers.
/// UNKNOWN/refusal returns no negative theorem.
pub fn certificate(n:usize,rows:Vec<Row>,cap:usize,byte_limit:usize)->Result<String,Error> {
    if n>32 || rows.len()>128 || rows.iter().any(|r|r.coefficients.len()!=n) {
        return Err(Error::Invalid("matrix shape/profile"));
    }
    if rows.iter().any(|r|r.coefficients.iter().chain(std::iter::once(&r.bound))
        .any(|q|q.to_string().len()>4096)) { return Err(Error::SourceLimit); }
    let decision=affine::solve(n,&rows,cap).map_err(Error::Invalid)?;
    let m=rows.len();
    let row_code=vector(rows.iter().map(row_literal).collect());
    let mut source=String::from("import G6RationalAffineWitness\nimport G6AffineContradictionCertificate\n\nopen UnifiedLean.G6.StrictAffineElimination\nopen UnifiedLean.G6.RationalAffineWitness\n");
    match decision {
        Decision::Unknown{..}=>return Err(Error::Unknown),
        Decision::Witness(witness)=>{
            if !affine::check_witness(n,&rows,&witness) {return Err(Error::Invalid("native witness"));}
            let v=vector(witness.iter().map(rational).collect());
            source.push_str(&format!(r#"
namespace ResearchCommons.Generated.AffineSAT
def rows : Fin {m} → Row {n} := {row_code}
def witness : Fin {n} → ℚ := {v}
theorem checked :
    checkRationalWitness (Finset.univ.image rows) witness = true := by decide
theorem real_feasible : ∃ x : Fin {n} → ℝ, ∀ i, (rows i).Holds x := by
  refine ⟨fun i => (witness i : ℝ), ?_⟩
  have h := rationalWitness_real (Finset.univ.image rows) witness
    ((checkRationalWitness_correct _ _).mp checked)
  intro i
  exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
end ResearchCommons.Generated.AffineSAT
"#));
        }
        Decision::Exclusion(weights)=>{
            if !affine::check_exclusion(n,&rows,&weights) {return Err(Error::Invalid("native exclusion"));}
            let v=vector(weights.iter().map(rational).collect());
            source.push_str(&format!(r#"
namespace ResearchCommons.Generated.AffineUNSAT
def rows : Fin {m} → Row {n} := {row_code}
def weights : Fin {m} → ℚ := {v}
theorem checked :
    UnifiedLean.G6.AffineContradictionCertificate.check rows weights = true := by decide
theorem real_infeasible : ¬ ∃ x : Fin {n} → ℝ, ∀ i, (rows i).Holds x :=
  UnifiedLean.G6.AffineContradictionCertificate.checked_excludes_real rows weights checked
end ResearchCommons.Generated.AffineUNSAT
"#));
        }
    }
    if source.len()>byte_limit {return Err(Error::SourceLimit);}
    Ok(source)
}
pub fn example(exclusion:bool)->Result<String,Error> {
    let rows=if exclusion {
        vec![
            Row{coefficients:vec![q(1,1)],bound:q(0,1),strict:true},
            Row{coefficients:vec![q(-1,1)],bound:q(0,1),strict:false},
            Row{coefficients:vec![q(-1,1)],bound:q(0,1),strict:false},
        ]
    }else{
        vec![
            Row{coefficients:vec![q(1,1)],bound:q(0,1),strict:false},
            Row{coefficients:vec![q(-1,1)],bound:q(0,1),strict:false},
            Row{coefficients:vec![q(-1,1)],bound:q(0,1),strict:false},
        ]
    };
    certificate(1,rows,4096,262144)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn weak_boundary_returns_checked_witness_source() {
        let source=example(false).unwrap();
        assert!(source.contains("def rows : Fin 3 → Row 1"));
        assert!(source.contains("theorem real_feasible"));
        assert!(!source.contains("real_infeasible"));
    }
    #[test] fn strict_boundary_returns_complete_multiplier_source() {
        let source=example(true).unwrap();
        assert!(source.contains("def weights : Fin 3 → ℚ"));
        assert!(source.contains("checked_excludes_real"));
    }
    #[test] fn resource_failure_is_not_a_no_certificate() {
        let rows=vec![
            Row{coefficients:vec![q(1,1)],bound:q(1,1),strict:false},
            Row{coefficients:vec![q(-1,1)],bound:q(0,1),strict:false}];
        assert_eq!(certificate(1,rows,0,262144),Err(Error::Unknown));
    }
    #[test] fn zero_dimension_and_empty_rows_have_literal_empty_carriers() {
        let source=certificate(0,vec![],0,262144).unwrap();
        assert!(source.contains("def rows : Fin 0 → Row 0 := Fin.elim0"));
        assert!(source.contains("def witness : Fin 0 → ℚ := Fin.elim0"));
    }
}

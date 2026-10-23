//! OLD finite coherent-parameter filter for supplied epoch arrays.
//! Exact Rational only. ONE hidden renaming is shared by adjacent matrices.
//! Structural checks are not canonical physical-source/observation admission.
use parity_solver::{q,Rational};
use crate::moments::literal;

#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Parameters{
 pub duration:Vec<Rational>,
 pub rates:Vec<Vec<Rational>>,
 pub routing:Vec<Vec<Vec<Rational>>>,
}
#[derive(Clone,Copy,Debug)]
pub struct Limits{
 pub epochs:usize,pub populations:usize,pub work:usize,pub results:usize,
 pub rational_chars:usize,pub source_bytes:usize,
}
impl Default for Limits{
 fn default()->Self{Self{epochs:64,populations:12,work:1_000_000,results:4096,
  rational_chars:4096,source_bytes:262144}}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error{Invalid(&'static str),Limit{kind:&'static str,required:usize,cap:usize}}
pub type Renaming=Vec<Vec<usize>>;
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct CompleteFilter{pub maps:Vec<Renaming>,pub checked_work:usize}
fn bound(kind:&'static str,n:usize,cap:usize)->Result<(),Error>{
 if n>cap{Err(Error::Limit{kind,required:n,cap})}else{Ok(())}
}
fn tick(work:&mut usize,limits:Limits)->Result<(),Error>{
 *work=work.checked_add(1).ok_or(Error::Limit{kind:"work",required:usize::MAX,cap:limits.work})?;
 bound("work",*work,limits.work)
}
fn rational(x:&Rational,limits:Limits)->Result<(),Error>{
 bound("rational_chars",x.to_string().len(),limits.rational_chars)
}
fn shape(p:&Parameters,limits:Limits)->Result<Vec<usize>,Error>{
 let j=p.duration.len();
 bound("epochs",j,limits.epochs)?;
 if p.rates.len()!=j.checked_add(1).ok_or(Error::Invalid("epoch count overflow"))?
   ||p.routing.len()!=j{return Err(Error::Invalid("epoch array dimensions"));}
 let counts=p.rates.iter().map(Vec::len).collect::<Vec<_>>();
 if counts.last()!=Some(&1){return Err(Error::Invalid("one root population required"));}
 for &n in &counts{
  if n==0{return Err(Error::Invalid("empty population carrier"));}
  bound("populations",n,limits.populations)?;
 }
 for d in &p.duration{rational(d,limits)?;if d<=&q(0,1){return Err(Error::Invalid("positive duration required"));}}
 for rates in &p.rates{for r in rates{
  rational(r,limits)?;if r<=&q(0,1){return Err(Error::Invalid("positive rate required"));}
 }}
 for (e,m) in p.routing.iter().enumerate(){
  if m.len()!=counts[e]||m.iter().any(|r|r.len()!=counts[e+1]){
   return Err(Error::Invalid("routing array dimensions"));
  }
  for row in m{
   for x in row{rational(x,limits)?;if x<&q(0,1){return Err(Error::Invalid("negative routing entry"));}}
   if row.iter().cloned().fold(q(0,1),|a,b|a+b)!=q(1,1){
    return Err(Error::Invalid("routing row must have mass one"));
   }
  }
  if (0..counts[e+1]).any(|k|m.iter().all(|r|r[k]==q(0,1))){
   return Err(Error::Invalid("unreachable output column"));
  }
 }
 Ok(counts)
}
fn permutations(a:&[Rational],b:&[Rational],limits:Limits,work:&mut usize)
 ->Result<Vec<Vec<usize>>,Error>{
 fn visit(a:&[Rational],b:&[Rational],limits:Limits,work:&mut usize,
  used:&mut [bool],prefix:&mut Vec<usize>,out:&mut Vec<Vec<usize>>)->Result<(),Error>{
  if prefix.len()==a.len(){
   bound("candidate permutations",out.len().saturating_add(1),limits.work)?;
   out.push(prefix.clone());return Ok(());
  }
  for k in 0..b.len(){
   tick(work,limits)?;
   if !used[k]&&a[prefix.len()]==b[k]{
    used[k]=true;prefix.push(k);
    visit(a,b,limits,work,used,prefix,out)?;
    prefix.pop();used[k]=false;
   }
  }Ok(())
 }
 let mut out=Vec::new();let mut used=vec![false;b.len()];
 visit(a,b,limits,work,&mut used,&mut Vec::new(),&mut out)?;Ok(out)
}
/// Every returned map is a complete tuple, fixing initial/root names. An
/// empty result means ONLY that these supplied arrays have no coherent
/// renaming. Refusal returns no partial filter and is never scientific NO.
pub fn filter(reference:&Parameters,candidate:&Parameters,limits:Limits)->Result<CompleteFilter,Error>{
 let counts=shape(reference,limits)?;
 if shape(candidate,limits)?!=counts{return Err(Error::Invalid("common aligned shape required"));}
 let mut work=0usize;
 for (a,b) in reference.duration.iter().zip(&candidate.duration){tick(&mut work,limits)?;if a!=b{
  return Ok(CompleteFilter{maps:Vec::new(),checked_work:work});
 }}
 let last=counts.len()-1;let mut choices=Vec::with_capacity(counts.len());
 for (j,&n) in counts.iter().enumerate(){
  if j==0||j==last{
   let mut valid=true;
   for i in 0..n{tick(&mut work,limits)?;valid&=reference.rates[j][i]==candidate.rates[j][i];}
   choices.push(if valid{vec![(0..n).collect()]}else{Vec::new()});
  }else{choices.push(permutations(&reference.rates[j],&candidate.rates[j],limits,&mut work)?);}
 }
 fn visit(j:usize,a:&Parameters,b:&Parameters,choices:&[Vec<Vec<usize>>],
  prefix:&mut Renaming,out:&mut Vec<Renaming>,work:&mut usize,l:Limits)->Result<(),Error>{
  if j==choices.len(){
   bound("results",out.len().saturating_add(1),l.results)?;
   out.push(prefix.clone());return Ok(());
  }
  for map in &choices[j]{
   tick(work,l)?;let mut valid=true;
   if j>0{
    let prev=&prefix[j-1];
    'entries:for i in 0..prev.len(){for k in 0..map.len(){
     tick(work,l)?;
     if a.routing[j-1][i][k]!=b.routing[j-1][prev[i]][map[k]]{valid=false;break 'entries;}
    }}
   }
   if valid{
    prefix.push(map.clone());visit(j+1,a,b,choices,prefix,out,work,l)?;prefix.pop();
   }
  }Ok(())
 }
 let mut maps=Vec::new();
 visit(0,reference,candidate,&choices,&mut Vec::new(),&mut maps,&mut work,limits)?;
 Ok(CompleteFilter{maps,checked_work:work})
}
fn vector(items:impl IntoIterator<Item=String>)->String{
 format!("![{}]",items.into_iter().collect::<Vec<_>>().join(", "))
}
fn render_parameters(name:&str,p:&Parameters)->String{
 let j=p.duration.len();
 let rates=p.rates.iter().map(|r|vector(r.iter().map(literal))).collect::<Vec<_>>();
 let matrices=p.routing.iter().map(|m|vector(m.iter().map(|r|vector(r.iter().map(literal))))).collect::<Vec<_>>();
 let mut s=format!("def {name} : Parameters {j} count where\n  duration := {}\n  rate := fun j => by\n    fin_cases j\n",
  vector(p.duration.iter().map(literal)));
 for r in rates{s.push_str(&format!("    · exact {r}\n"));}
 s.push_str("  routing := fun j => by\n    fin_cases j\n");
 for m in matrices{s.push_str(&format!("    · exact {m}\n"));}s
}
/// Entire result certificate on the actual supplied arrays. Native validation
/// is not assumed to be a bijection onto physical histories, and the checker
/// proves the exact finite parameter equations rather than a desired law.
pub fn lean_certificate(reference:&Parameters,candidate:&Parameters,name:&str,limits:Limits)->Result<String,Error>{
 if name.is_empty()||!name.bytes().all(|c|c.is_ascii_alphanumeric()||c==b'_'){
  return Err(Error::Invalid("certificate name"));
 }
 let result=filter(reference,candidate,limits)?;let j=reference.duration.len();
 // An empty boundary carrier has no routing cases and needs Fin.elim0.
 let mut s=format!("import ResearchCommons.MSCI.Alignment\nimport Mathlib.Tactic\n\nnamespace ResearchCommons.Generated.MSCIAlignment_{name}\nopen ResearchCommons.MSCI.Alignment\nset_option maxHeartbeats 3000000\nset_option maxRecDepth 10000\n");
 s.push_str(&format!("def count : Fin {} → ℕ := {}\n",j+1,vector(reference.rates.iter().map(|r|r.len().to_string()))));
 for (name,p) in [("reference",reference),("candidate",candidate)]{
  let mut body=render_parameters(name,p);
  if j==0{
   body=body.replace("duration := ![]","duration := Fin.elim0")
    .replace("  routing := fun j => by\n    fin_cases j\n","  routing := Fin.elim0\n");
  }s.push_str(&body);
 }
 for (i,sigma) in result.maps.iter().enumerate(){
  s.push_str(&format!("def rename{i} : Rename {j} count := fun j => by\n  fin_cases j\n"));
  for map in sigma{s.push_str(&format!("  · exact {}\n",vector(map.iter().map(usize::to_string))));}
 }
 let supplied=if result.maps.is_empty(){"∅".to_string()}else{
  format!("{{{}}}",(0..result.maps.len()).map(|i|format!("rename{i}")).collect::<Vec<_>>().join(", "))
 };
 s.push_str(&format!("def nativeResult : Finset (Rename {j} count) := {supplied}\n"));
 s.push_str(&format!("theorem entire_native_filter_checked :\n    allAlignments {j} count reference candidate = nativeResult := by\n  decide\n"));
 s.push_str(&format!("theorem every_map_and_omission_checked (sigma : Rename {j} count) :\n    Matches {j} count reference candidate sigma ↔ sigma ∈ nativeResult := by\n  rw [← mem_allAlignments_iff, entire_native_filter_checked]\n"));
 s.push_str(&format!("theorem returned_nonempty_iff_exact_parameter_match :\n    nativeResult.Nonempty ↔ ∃ sigma, Matches {j} count reference candidate sigma := by\n  rw [← entire_native_filter_checked, allAlignments_nonempty_iff]\n"));
 s.push_str(&format!("#check every_map_and_omission_checked\n#check returned_nonempty_iff_exact_parameter_match\nend ResearchCommons.Generated.MSCIAlignment_{name}\n"));
 bound("source_bytes",s.len(),limits.source_bytes)?;Ok(s)
}
pub fn retained_fixture()->Parameters{
 Parameters{
  duration:vec![q(1,1),q(2,1),q(3,1)],
  rates:vec![vec![q(1,1),q(2,1)],vec![q(2,3),q(2,3)],
   vec![q(2,3),q(2,3)],vec![q(3,4)]],
  routing:vec![
   vec![vec![q(1,4),q(3,4)],vec![q(2,3),q(1,3)]],
   vec![vec![q(1,5),q(4,5)],vec![q(3,7),q(4,7)]],
   vec![vec![q(1,1)],vec![q(1,1)]]],
 }
}
pub fn example(incoherent:bool)->Result<String,Error>{
 let a=retained_fixture();let mut b=a.clone();
 if incoherent{b.routing[1].reverse();}else{
  // Relabel one hidden population carrier on BOTH its input and output.
  for row in &mut b.routing[0]{row.reverse();}
  b.routing[1].reverse();
 }
 lean_certificate(&a,&b,if incoherent{"Incoherent"}else{"Coherent"},Limits::default())
}
#[cfg(test)]mod tests{
 use super::*;
 #[test]fn whole_coherent_epoch_filter_preserves_ties_zeros_equal_rates_and_expansion(){
  let a=retained_fixture();let l=Limits::default();
  let same=filter(&a,&a,l).unwrap();
  assert_eq!(same.maps,vec![vec![vec![0,1],vec![0,1],vec![0,1],vec![0]]]);
  let mut true_b=a.clone();for row in &mut true_b.routing[0]{row.reverse();}true_b.routing[1].reverse();
  let yes=filter(&a,&true_b,l).unwrap();
  assert_eq!(yes.maps,vec![vec![vec![0,1],vec![1,0],vec![0,1],vec![0]]]);
  let mut false_b=a.clone();false_b.routing[1].reverse();
  assert!(filter(&a,&false_b,l).unwrap().maps.is_empty());
  let expansion=Parameters{duration:vec![q(1,1),q(1,1)],
   rates:vec![vec![q(1,1)],vec![q(1,1),q(1,1)],vec![q(1,1)]],
   routing:vec![vec![vec![q(1,2),q(1,2)]],vec![vec![q(1,1)],vec![q(1,1)]]]};
  assert_eq!(filter(&expansion,&expansion,l).unwrap().maps.len(),2);
  let mut zeros=a.clone();zeros.routing[0]=vec![vec![q(1,1),q(0,1)],vec![q(0,1),q(1,1)]];
  assert_eq!(filter(&zeros,&zeros,l).unwrap().maps.len(),1);
  let root=Parameters{duration:vec![],rates:vec![vec![q(1,1)]],routing:vec![]};
  assert_eq!(filter(&root,&root,l).unwrap().maps,vec![vec![vec![0]]]);
  assert!(lean_certificate(&root,&root,"Root",l).unwrap().contains("routing := Fin.elim0"));
 }
 #[test]fn no_partial_filter_or_certificate_on_invalid_dimensions_or_resource_refusal(){
  let a=retained_fixture();let l=Limits::default();
  assert!(matches!(filter(&a,&a,Limits{work:1,..l}),Err(Error::Limit{..})));
  assert!(matches!(filter(&a,&a,Limits{results:0,..l}),Err(Error::Limit{..})));
  assert!(matches!(lean_certificate(&a,&a,"Small",Limits{source_bytes:1,..l}),Err(Error::Limit{..})));
  let mut b=a.clone();b.routing[0][0]=vec![q(1,1)];
  assert!(matches!(filter(&a,&b,l),Err(Error::Invalid(_))));
  let mut b=a.clone();b.routing[0][0][0]=q(-1,4);
  assert!(matches!(filter(&a,&b,l),Err(Error::Invalid(_))));
  let mut b=a.clone();b.duration[0]=q(0,1);
  assert!(matches!(filter(&a,&b,l),Err(Error::Invalid(_))));
  assert!(matches!(lean_certificate(&a,&a,"Bad\naxiom",l),Err(Error::Invalid(_))));
  let doc=example(false).unwrap();let no=example(true).unwrap();
  assert!(doc.contains("every_map_and_omission_checked"));
  assert!(no.contains("nativeResult : Finset (Rename 3 count) := ∅"));
  assert!(!doc.contains("native_decide")&&!doc.contains("sorry"));
 }
}

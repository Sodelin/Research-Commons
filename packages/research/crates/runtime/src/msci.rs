//! Exact implementation of the RETAINED bounded-MSCI observation cutoff.
//! This calculates a sufficient hand-theorem bound; it is not a source
//! admission, likelihood engine, parameter classifier or data recommendation.
//! All arithmetic reuses the original arbitrary-precision Rational, with
//! denominator one throughout. Profile refusals are UNKNOWN, never NO.
use parity_solver::{q,Rational};

#[derive(Clone,Copy,Debug)]
pub struct Limits{
 pub copies:usize,pub epochs:usize,pub populations:usize,
 pub integer_chars:usize,pub arithmetic_operations:usize,
}
impl Default for Limits{
 fn default()->Self{Self{copies:128,epochs:256,populations:65536,
  integer_chars:8192,arithmetic_operations:200000}}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error{
 Invalid(&'static str),
 Limit{resource:&'static str,required:usize,cap:usize},
 Overflow,
}
fn bound(resource:&'static str,required:usize,cap:usize)->Result<(),Error>{
 if required>cap{Err(Error::Limit{resource,required,cap})}else{Ok(())}
}
struct Arithmetic{limits:Limits,operations:usize}
impl Arithmetic{
 fn spend(&mut self)->Result<(),Error>{
  self.operations=self.operations.checked_add(1).ok_or(Error::Overflow)?;
  bound("arithmetic_operations",self.operations,self.limits.arithmetic_operations)
 }
 fn check(&self,n:&Rational)->Result<(),Error>{
  bound("integer_chars",n.numer().to_string().len(),self.limits.integer_chars)
 }
 fn natural(&self,n:usize)->Result<Rational,Error>{
  let n=i64::try_from(n).map_err(|_|Error::Overflow)?;
  let value=q(n,1);self.check(&value)?;Ok(value)
 }
 fn add(&mut self,a:&Rational,b:&Rational)->Result<Rational,Error>{
  self.spend()?;let v=a+b;self.check(&v)?;Ok(v)
 }
 fn mul(&mut self,a:&Rational,b:&Rational)->Result<Rational,Error>{
  self.spend()?;
  if a!=&q(0,1)&&b!=&q(0,1){
   let least=a.numer().to_string().len().checked_add(b.numer().to_string().len())
    .and_then(|n|n.checked_sub(1)).ok_or(Error::Overflow)?;
   // A nonnegative integer product needs at least this many digits.
   // Refuse before a provably oversized product; the boundary multiplication
   // may produce one excess digit, checked immediately below.
   bound("integer_chars",least,self.limits.integer_chars)?;
  }
  let v=a*b;self.check(&v)?;Ok(v)
 }
 fn pow(&mut self,a:&Rational,mut exponent:usize)->Result<Rational,Error>{
  let mut answer=q(1,1);let mut base=a.clone();self.check(&answer)?;self.check(&base)?;
  while exponent!=0{
   if exponent&1==1{answer=self.mul(&answer,&base)?;}
   exponent>>=1;
   if exponent!=0{base=self.mul(&base,&base)?;}
  }
  Ok(answer)
 }
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct ObservationCutoff{
 copies:usize,epochs:usize,populations:usize,
 bell:Rational,states:Rational,paths:Rational,denominator_degree:Rational,
 terms:Rational,recurrence_order:Rational,balanced_columns:Rational,locus_length:Rational,
 operations:usize,
}
impl ObservationCutoff{
 pub fn locus_length(&self)->&Rational{&self.locus_length}
 pub fn recurrence_order(&self)->&Rational{&self.recurrence_order}
 pub fn state_bound(&self)->&Rational{&self.states}
 pub fn operations(&self)->usize{self.operations}
 pub fn json(&self)->Result<String,Error>{
  serde_json::to_string_pretty(&serde_json::json!({
   "schema":1,"kind":"retained-bounded-msci-sufficient-cutoff",
   "n":self.copies,"J":self.epochs,"P":self.populations,
   "Bell":self.bell.to_string(),"S":self.states.to_string(),"E":self.paths.to_string(),
   "F":self.denominator_degree.to_string(),"M":self.terms.to_string(),
   "K":self.recurrence_order.to_string(),"A":self.balanced_columns.to_string(),
   "L":self.locus_length.to_string(),"arithmetic_operations":self.operations,
   "source_admission_verified":false,"full_bridge_lean_verified":false,
   "scope":"Sufficient cutoff from the retained complete hand theorem, conditional on actual bounded finite current-block pulse source, shared parameter ties, contemporaneous labelled panel and normalized homogeneous clock-JC observation. No arbitrary-network likelihood, parameter identifiability, source admission, finite-data accuracy or universal native refinement is inferred."
  })).map_err(|_|Error::Invalid("cutoff JSON"))
 }
}
/// The original theorem uses S=Bell(n)P^n; E=sum_{i<n} choose(n,2)^i;
/// F=J*S^2+S; M=E*(n*E*S)^J; K=2M(2F+1); L=4^(n-1)(K-1).
/// The NEW implementation is bounded arithmetic only. It does not increase
/// the separate retained native source/copy/word profiles.
pub fn observation_cutoff(n:usize,epochs:usize,populations:usize,limits:Limits)
 ->Result<ObservationCutoff,Error>{
 if n<2{return Err(Error::Invalid("the bounded observation theorem requires n>=2"));}
 if populations==0{return Err(Error::Invalid("positive population bound required"));}
 if limits.integer_chars==0{return Err(Error::Invalid("positive integer rendering limit required"));}
 bound("copies",n,limits.copies)?;bound("epochs",epochs,limits.epochs)?;
 bound("populations",populations,limits.populations)?;
 // Check work/array width before allocating the Stirling row.
 let width=n.checked_add(1).ok_or(Error::Overflow)?;
 let stirling_steps=n.checked_mul(width).ok_or(Error::Overflow)?;
 bound("arithmetic_operations",stirling_steps,limits.arithmetic_operations)?;
 let mut a=Arithmetic{limits,operations:0};
 let mut row=vec![q(0,1);width];row[0]=q(1,1);
 for i in 1..=n{
  for k in (1..=i).rev(){
   let kq=a.natural(k)?;
   let product=a.mul(&kq,&row[k])?;
   row[k]=a.add(&row[k-1],&product)?;
  }
  row[0]=q(0,1);
 }
 let mut bell=q(0,1);for v in row{bell=a.add(&bell,&v)?;}
 let nq=a.natural(n)?;let pq=a.natural(populations)?;let jq=a.natural(epochs)?;
 let power=a.pow(&pq,n)?;let states=a.mul(&bell,&power)?;
 let pairs=n.checked_mul(n-1).ok_or(Error::Overflow)?/2;let b=a.natural(pairs)?;
 let mut paths=q(0,1);let mut term=q(1,1);
 for i in 0..n{paths=a.add(&paths,&term)?;if i+1<n{term=a.mul(&term,&b)?;}}
 let square=a.mul(&states,&states)?;let jsquare=a.mul(&jq,&square)?;
 let denominator_degree=a.add(&jsquare,&states)?;
 let ne=a.mul(&nq,&paths)?;let nes=a.mul(&ne,&states)?;
 let power=a.pow(&nes,epochs)?;let terms=a.mul(&paths,&power)?;
 let twice_f=a.mul(&q(2,1),&denominator_degree)?;
 let factor=a.add(&twice_f,&q(1,1))?;let twice_m=a.mul(&q(2,1),&terms)?;
 let recurrence_order=a.mul(&twice_m,&factor)?;
 let balanced_columns=a.pow(&q(4,1),n-1)?;
 if recurrence_order<q(1,1){return Err(Error::Invalid("internal positive recurrence order"));}
 a.spend()?;let previous=&recurrence_order-q(1,1);a.check(&previous)?;
 let locus_length=a.mul(&balanced_columns,&previous)?;
 Ok(ObservationCutoff{copies:n,epochs,populations,bell,states,paths,denominator_degree,
  terms,recurrence_order,balanced_columns,locus_length,operations:a.operations})
}
#[cfg(test)]mod tests{
 use super::*;
 fn text(r:&Rational)->String{r.to_string()}
 #[test]fn exact_retained_integer_controls_including_an_output_larger_than_machine_integers(){
  // Copied from immutable5Oct CONTROL-RESULTS Gitblob35eec264; no producer rerun.
  let expected=[
   (2,0,1,["2","2","2","2","20","76"]),
   (3,2,3,["135","13","36585","360362925","52736231170350","843779698725584"]),
   (6,3,5,["3171875","813616","30182376218750",
    "3020507128752775232931660258000000000000000000",
    "364664330125736471168259643210520621070516000000000000000000",
    "373416274048754146476297874647573115976208383999999999999998976"]),
  ];
  for(n,j,p,values)in expected{
   let b=observation_cutoff(n,j,p,Limits::default()).unwrap();
   let actual=[&b.states,&b.paths,&b.denominator_degree,&b.terms,&b.recurrence_order,&b.locus_length]
    .map(text);
   assert_eq!(actual,values.map(str::to_owned));
   let json:serde_json::Value=serde_json::from_str(&b.json().unwrap()).unwrap();
   assert_eq!(json["n"],n);assert_eq!(json["source_admission_verified"],false);
  }
 }
 #[test]fn invalid_contract_and_profile_limits_never_become_a_negative_identifiability_claim(){
  assert!(matches!(observation_cutoff(1,0,1,Limits::default()),Err(Error::Invalid(_))));
  assert!(matches!(observation_cutoff(2,0,0,Limits::default()),Err(Error::Invalid(_))));
  assert!(matches!(observation_cutoff(3,2,3,Limits{copies:2,..Limits::default()}),
   Err(Error::Limit{resource:"copies",..})));
  assert!(matches!(observation_cutoff(3,2,3,Limits{integer_chars:4,..Limits::default()}),
   Err(Error::Limit{resource:"integer_chars",..})));
  assert!(matches!(observation_cutoff(6,3,5,Limits{arithmetic_operations:2,..Limits::default()}),
   Err(Error::Limit{resource:"arithmetic_operations",..})));
 }
}

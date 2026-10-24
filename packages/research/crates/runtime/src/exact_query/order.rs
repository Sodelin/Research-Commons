//! Bounded production port of the retained adaptive_order/insertion/recover_all.
//! Existing mathematics/algorithm, not a new circle learner or source oracle.
//! Tree identities are private signed nodes; taxon data remain original u64.
use super::{Error,Limits,Quartet,Recovery,pair_bit};
use std::collections::{BTreeMap,BTreeSet};
type Node=i128;
#[derive(Clone,Copy,Debug)]
pub struct OrderLimits {
    pub search:Limits,
    /// Explicit cumulative adjacency/rotation/search work, not a wall-time claim.
    pub tree_work:usize,
}
impl Default for OrderLimits {
    fn default()->Self {Self{search:Limits::default(),tree_work:16_777_216}}
}
#[derive(Debug,PartialEq,Eq)]
pub struct JointRecovery {
    pub circle:Vec<u64>,
    pub recovery:Recovery,
    pub order_queries:usize,
    pub sparse_requests:usize,
    pub order_predicates:usize,
    pub centroid_steps:usize,
    pub internal_vertices:usize,
    pub retired_vertices:usize,
    pub tree_work:usize,
}
struct Work { used:usize, limit:usize }
impl Work {
    fn tick<E>(&mut self)->Result<(),Error<E>> {
        if self.used>=self.limit {return Err(Error::Unknown("order tree work limit"));}
        self.used+=1;Ok(())
    }
}
struct Tree { rot:BTreeMap<Node,Vec<Node>>,taxa:BTreeSet<Node>,next:Node }
impl Tree {
    fn new<E>(labels:&[u64])->Result<Self,Error<E>> {
        if labels.len()!=3 {return Err(Error::Invalid("initial order arity"));}
        let ns:Vec<_>=labels.iter().map(|x|Node::from(*x)).collect();
        let mut rot=BTreeMap::from([(-1,ns.clone())]);
        for n in &ns {rot.insert(*n,vec![-1]);}
        Ok(Self{rot,taxa:ns.into_iter().collect(),next:-2})
    }
    fn neighbors<E>(&self,v:Node)->Result<&[Node],Error<E>> {
        self.rot.get(&v).map(Vec::as_slice).ok_or(Error::Invalid("missing rotation node"))
    }
    fn fresh<E>(&mut self)->Result<Node,Error<E>> {
        let n=self.next;self.next=self.next.checked_sub(1).ok_or(Error::Unknown("tree identity overflow"))?;Ok(n)
    }
    fn component<E>(&self,start:Node,blocked:Option<Node>,allowed:Option<&BTreeSet<Node>>,w:&mut Work)
        ->Result<BTreeSet<Node>,Error<E>> {
        let permitted=|v|self.rot.contains_key(&v)&&allowed.is_none_or(|a|a.contains(&v));
        if Some(start)==blocked||!permitted(start){return Ok(BTreeSet::new());}
        let mut seen=BTreeSet::from([start]);let mut todo=vec![start];
        while let Some(v)=todo.pop(){w.tick()?;
            for &u in self.neighbors(v)? {w.tick()?;
                if Some(u)!=blocked&&permitted(u)&&seen.insert(u){todo.push(u);}
            }
        }Ok(seen)
    }
    fn validate<E>(&self,w:&mut Work)->Result<(),Error<E>> {
        let mut degrees=0usize;
        for (&v,ns) in &self.rot {w.tick()?;
            if ns.iter().collect::<BTreeSet<_>>().len()!=ns.len()||
                (self.taxa.contains(&v)&&ns.len()!=1)||(!self.taxa.contains(&v)&&ns.len()<3){
                return Err(Error::Invalid("rotation tree degree/promise"));
            }
            degrees=degrees.checked_add(ns.len()).ok_or(Error::Unknown("degree overflow"))?;
            for &u in ns {w.tick()?;if !self.neighbors(u)?.contains(&v){return Err(Error::Invalid("asymmetric tree"));}}
        }
        let edges=self.rot.len().checked_sub(1).and_then(|n|n.checked_mul(2)).ok_or(Error::Unknown("tree size overflow"))?;
        if degrees!=edges||self.rot.len()-self.taxa.len()>self.taxa.len()-2{
            return Err(Error::Invalid("rotation tree census"));
        }
        let root=*self.rot.keys().next().ok_or(Error::Invalid("empty tree"))?;
        if self.component(root,None,None,w)?.len()!=self.rot.len(){return Err(Error::Invalid("disconnected tree"));}
        Ok(())
    }
    fn representatives<E>(&self,v:Node,w:&mut Work)->Result<Vec<u64>,Error<E>> {
        if self.taxa.contains(&v){return Err(Error::Invalid("leaf has no rotation"));}
        self.neighbors(v)?.iter().map(|&u|{
            let comp=self.component(u,Some(v),None,w)?;
            let t=*comp.intersection(&self.taxa).next().ok_or(Error::Invalid("empty taxon component"))?;
            u64::try_from(t).map_err(|_|Error::Invalid("tree identity used as taxon"))
        }).collect()
    }
    fn one_order<E>(&self,w:&mut Work)->Result<Vec<u64>,Error<E>> {
        let root=*self.taxa.first().ok_or(Error::Invalid("empty taxa"))?;
        let mut out=vec![u64::try_from(root).map_err(|_|Error::Invalid("root label"))?];
        let parent=*self.neighbors(root)?.first().ok_or(Error::Invalid("isolated taxon"))?;
        let mut stack=vec![(parent,root)];let mut visited=BTreeSet::from([root]);
        while let Some((v,parent))=stack.pop(){w.tick()?;
            if !visited.insert(v){return Err(Error::Invalid("rotation cycle"));}
            if self.taxa.contains(&v){out.push(u64::try_from(v).map_err(|_|Error::Invalid("taxon label"))?);continue;}
            let ns=self.neighbors(v)?;let i=ns.iter().position(|x|*x==parent).ok_or(Error::Invalid("rotation parent"))?;
            let children:Vec<_>=ns[i+1..].iter().chain(&ns[..i]).copied().collect();
            for u in children.into_iter().rev(){stack.push((u,v));}
        }
        if out.len()!=self.taxa.len(){return Err(Error::Invalid("order leaf coverage"));}
        let mut reverse=vec![out[0]];reverse.extend(out[1..].iter().rev());
        if reverse<out {out=reverse;}Ok(out)
    }
    fn replace<E>(&mut self,v:Node,old:Node,new:Node)->Result<(),Error<E>> {
        let ns=self.rot.get_mut(&v).ok_or(Error::Invalid("rotation replace node"))?;
        let i=ns.iter().position(|x|*x==old).ok_or(Error::Invalid("rotation replace edge"))?;
        ns[i]=new;Ok(())
    }
    fn subdivide<E>(&mut self,u:Node,v:Node,z:u64,w:&mut Work)->Result<(),Error<E>> {
        let z=Node::from(z);if self.rot.contains_key(&z){return Err(Error::Invalid("repeated taxon"));}
        let t=self.fresh()?;self.replace(u,v,t)?;self.replace(v,u,t)?;
        self.rot.insert(t,vec![u,z,v]);self.rot.insert(z,vec![t]);self.taxa.insert(z);self.validate(w)
    }
    fn marker<E>(rotation:&[Node],corner:[Node;2],z:Node,w:&mut Work)->Result<Vec<Node>,Error<E>> {
        for (i,&u) in rotation.iter().enumerate(){w.tick()?;let v=rotation[(i+1)%rotation.len()];
            if (u==corner[0]&&v==corner[1])||(u==corner[1]&&v==corner[0]){
                let mut out=rotation[..=i].to_vec();out.push(z);out.extend(&rotation[i+1..]);return Ok(out);
            }
        }Err(Error::Invalid("not a rotation corner"))
    }
    fn without<E>(rotation:&[Node],neighbor:Node)->Result<Vec<Node>,Error<E>> {
        let i=rotation.iter().position(|x|*x==neighbor).ok_or(Error::Invalid("path rotation neighbor"))?;
        Ok(rotation[i+1..].iter().chain(&rotation[..i]).copied().collect())
    }
    fn merge_path<E>(&mut self,path:&[Node],corners:&BTreeMap<Node,[Node;2]>,z:u64,w:&mut Work)->Result<(),Error<E>> {
        let z=Node::from(z);
        if path.is_empty()||path.iter().collect::<BTreeSet<_>>().len()!=path.len()||self.rot.contains_key(&z){
            return Err(Error::Invalid("central path/promise"));
        }
        let corner=|v|corners.get(&v).copied().ok_or(Error::Invalid("missing central corner"));
        let mut seq=Self::marker(self.neighbors(path[0])?,corner(path[0])?,z,w)?;
        for pair in path.windows(2){w.tick()?;
            let (prev,v)=(pair[0],pair[1]);let left=Self::without(&seq,v)?;
            let initial=Self::marker(self.neighbors(v)?,corner(v)?,z,w)?;let mut chosen=None;
            for mut orient in [initial.clone(),initial.into_iter().rev().collect()] {
                let right=Self::without(&orient,prev)?;orient=left.iter().chain(&right).copied().collect();
                let positions:Vec<_>=orient.iter().enumerate().filter_map(|(i,x)|(*x==z).then_some(i)).collect();
                if positions.len()!=2 {return Err(Error::Invalid("central marker count"));}
                let (i,j)=(positions[0],positions[1]);
                if j-i==1||(i==0&&j==orient.len()-1){orient.remove(j);chosen=Some(orient);break;}
            }
            seq=chosen.ok_or(Error::Invalid("central markers do not meet"))?;
        }
        let paths:BTreeSet<_>=path.iter().copied().collect();
        if seq.iter().collect::<BTreeSet<_>>().len()!=seq.len()||seq.iter().any(|u|paths.contains(u)){
            return Err(Error::Invalid("merged rotation/promise"));
        }
        let t=self.fresh()?;
        for &u in &seq {w.tick()?;if u==z{continue;}
            let old:Vec<_>=self.neighbors(u)?.iter().filter(|v|paths.contains(v)).copied().collect();
            if old.len()!=1{return Err(Error::Invalid("central external incidence"));}
            self.replace(u,old[0],t)?;
        }
        for v in path{self.rot.remove(v);}
        self.rot.insert(t,seq);self.rot.insert(z,vec![t]);self.taxa.insert(z);self.validate(w)
    }
}
struct Shared<F> {
    oracle:F,labels:BTreeSet<u64>,cache:BTreeMap<Quartet,u8>,
    trace:Vec<(Quartet,u8)>,limit:usize,
}
impl<F,E> Shared<F> where F:FnMut(Quartet)->Result<u8,E> {
    fn ask(&mut self,mut q:Quartet)->Result<u8,Error<E>> {
        q.sort_unstable();
        if q.windows(2).any(|x|x[0]==x[1])||q.iter().any(|x|!self.labels.contains(x)){
            return Err(Error::Invalid("illegal original quartet"));
        }
        if let Some(&a)=self.cache.get(&q){return Ok(a);}
        if self.cache.len()>=self.limit{return Err(Error::Unknown("shared distinct quartet query limit"));}
        let a=(self.oracle)(q).map_err(Error::Oracle)?;
        if !(1..=6).contains(&a){return Err(Error::Invalid("nonempty circular binary support promise"));}
        self.cache.insert(q,a);self.trace.push((q,a));Ok(a)
    }
}
struct Learner<'a,F> {
    shared:&'a mut Shared<F>,tree:Tree,work:Work,reps:BTreeMap<Node,Vec<u64>>,
    z:u64,predicates:usize,predicate_limit:usize,centroids:usize,retired:usize,
}
impl<F,E> Learner<'_,F> where F:FnMut(Quartet)->Result<u8,E> {
    fn ask(&mut self,q:Quartet)->Result<u8,Error<E>> {
        if self.predicates>=self.predicate_limit{return Err(Error::Unknown("order predicate limit"));}
        self.predicates+=1;self.shared.ask(q)
    }
    fn reps(&mut self,v:Node)->Result<Vec<u64>,Error<E>> {
        if let Some(x)=self.reps.get(&v){return Ok(x.clone());}
        let x=self.tree.representatives(v,&mut self.work)?;self.reps.insert(v,x.clone());Ok(x)
    }
    fn filter(&mut self,order:&[u64],mut cuts:[usize;3],answer:u8,gaps:&BTreeSet<usize>)->Result<BTreeSet<usize>,Error<E>> {
        cuts.sort_unstable();let [i,j,k]=cuts;
        if i==j||j==k||k>=order.len(){return Err(Error::Invalid("distinct insertion cuts"));}
        let mut q=[self.z,order[i],order[j],order[k]];q.sort_unstable();
        let bits=[pair_bit::<E>(q,[self.z,order[k]])?,pair_bit::<E>(q,[self.z,order[i]])?,pair_bit::<E>(q,[self.z,order[j]])?];
        let mut out=BTreeSet::new();
        for &g in gaps {self.work.tick()?;let which=if i<=g&&g<j{0}else if j<=g&&g<k{1}else{2};
            if answer&bits[which]==0{out.insert(g);}
        }Ok(out)
    }
    fn gaps(&mut self,order:&[u64],promised:bool)->Result<BTreeSet<usize>,Error<E>> {
        let m=order.len();let mut cand:BTreeSet<_>=(0..m).collect();
        while cand.len()>2 {self.work.tick()?;
            let s:Vec<_>=cand.iter().copied().collect();let n=s.len();let cuts=[s[0],s[n/3],s[2*n/3]];
            let answer=self.ask([self.z,order[cuts[0]],order[cuts[1]],order[cuts[2]]])?;
            let next=self.filter(order,cuts,answer,&cand)?;
            if next.len()>=cand.len(){return Err(Error::Invalid("insertion reduction/promise"));}
            cand=next;
        }
        if promised&&cand.len()<=1{return Ok(cand);}
        let mut kept=BTreeSet::new();
        for &i in &cand {self.work.tick()?;let (b,c)=(order[i],order[(i+1)%m]);
            let tests=if promised {
                let j=*cand.iter().find(|x|**x!=i).ok_or(Error::Invalid("other promised gap"))?;
                vec![order[j],order[(j+1)%m]]
            }else{order.to_vec()};
            let mut ok=true;
            for a in tests {self.work.tick()?;if a==b||a==c{continue;}
                let mut q=[self.z,a,b,c];q.sort_unstable();
                if self.ask(q)?&pair_bit::<E>(q,[self.z,a])?!=0{ok=false;break;}
            }
            if ok{kept.insert(i);}
        }Ok(kept)
    }
    fn arrow(&mut self,v:Node,u:Node)->Result<bool,Error<E>> {
        if self.tree.taxa.contains(&v){return Ok(true);}
        let ns=self.tree.neighbors(v)?.to_vec();let i=ns.iter().position(|x|*x==u).ok_or(Error::Invalid("arrow neighbor"))?;
        let r=self.reps(v)?;let d=r.len();let mut q=[self.z,r[(i+d-1)%d],r[i],r[(i+1)%d]];q.sort_unstable();
        Ok(self.ask(q)?==pair_bit::<E>(q,[self.z,r[i]])?)
    }
    fn corner(&mut self,v:Node)->Result<[Node;2],Error<E>> {
        let r=self.reps(v)?;let gaps=self.gaps(&r,true)?;
        if gaps.len()!=1{return Err(Error::Invalid("not central under original promise"));}
        let i=*gaps.first().ok_or(Error::Invalid("empty central gap"))?;let ns=self.tree.neighbors(v)?;
        Ok([ns[i],ns[(i+1)%ns.len()]])
    }
    fn classify(&mut self,v:Node,weights:&BTreeMap<Node,usize>)->Result<Option<Node>,Error<E>> {
        if self.tree.taxa.contains(&v){return Ok(self.tree.neighbors(v)?.first().copied());}
        let ns=self.tree.neighbors(v)?.to_vec();let r=self.reps(v)?;let d=ns.len();
        let mut gaps:BTreeSet<_>=(0..d).collect();
        let mut active:BTreeSet<_>=(0..d).filter(|i|weights.get(&ns[*i]).copied().unwrap_or(0)>0).collect();
        while !active.is_empty(){self.work.tick()?;
            let weight=|i:usize|weights.get(&ns[i]).copied().unwrap_or(0);
            let total:usize=active.iter().map(|&i|weight(i)).sum();
            let heavy=*active.iter().max_by(|a,b|weight(**a).cmp(&weight(**b)).then_with(||b.cmp(a)))
                .ok_or(Error::Invalid("empty active arrows"))?;
            let is_heavy=6*(weight(heavy) as u128)>total as u128;
            let cuts=if is_heavy {[(heavy+d-1)%d,heavy,(heavy+1)%d]}else{
                let mut chunks:Vec<Vec<usize>>=vec![];let mut cur=vec![];let mut sum=0usize;
                for &i in &active {self.work.tick()?;cur.push(i);sum+=weight(i);
                    if chunks.len()<2&&4*(sum as u128)>=total as u128 {chunks.push(cur);cur=vec![];sum=0;}
                }chunks.push(cur);
                if chunks.len()!=3||chunks.iter().any(|x|x.is_empty()||
                    6*x.iter().map(|&i|weight(i) as u128).sum::<u128>()<total as u128){
                    return Err(Error::Invalid("balanced arrow cuts"));
                }[chunks[0][0],chunks[1][0],chunks[2][0]]
            };
            let mut q=[self.z,r[cuts[0]],r[cuts[1]],r[cuts[2]]];q.sort_unstable();let ans=self.ask(q)?;
            if is_heavy&&ans==pair_bit::<E>(q,[self.z,r[heavy]])?{return Ok(Some(ns[heavy]));}
            gaps=self.filter(&r,cuts,ans,&gaps)?;
            active.retain(|i|gaps.contains(i)&&gaps.contains(&((i+d-1)%d)));
            let after:usize=active.iter().map(|&i|weight(i)).sum();
            if 6*(after as u128)>5*(total as u128){return Err(Error::Invalid("arrow weight reduction/promise"));}
        }Ok(None)
    }
    fn central(&mut self)->Result<(Node,Option<Node>),Error<E>> {
        let mut region:BTreeSet<_>=self.tree.rot.keys().copied().collect();
        while !region.is_empty(){self.work.tick()?;self.centroids+=1;
            let root=*region.first().ok_or(Error::Invalid("empty central region"))?;
            let mut parent=BTreeMap::from([(root,None)]);let mut traversal=vec![root];let mut cursor=0;
            while cursor<traversal.len(){self.work.tick()?;let x=traversal[cursor];cursor+=1;
                for &y in self.tree.neighbors(x)? {self.work.tick()?;
                    if region.contains(&y)&&parent[&x]!=Some(y){
                        if parent.insert(y,Some(x)).is_some(){return Err(Error::Invalid("central region cycle"));}
                        traversal.push(y);
                    }
                }
            }
            if traversal.len()!=region.len(){return Err(Error::Invalid("central region disconnected"));}
            let mut sizes:BTreeMap<_,usize>=region.iter().map(|&x|(x,1)).collect();
            for &x in traversal[1..].iter().rev(){self.work.tick()?;
                let p=parent[&x].ok_or(Error::Invalid("central parent"))?;let n=sizes[&x];
                *sizes.get_mut(&p).ok_or(Error::Invalid("central size"))?+=n;
            }
            let mut best:Option<(usize,Node,BTreeMap<Node,usize>)>=None;
            for &x in &region {self.work.tick()?;
                let weights:BTreeMap<_,_>=self.tree.neighbors(x)?.iter().map(|&y|{
                    let value=if parent.get(&y)==Some(&Some(x)){sizes[&y]}
                        else if parent[&x]==Some(y){region.len()-sizes[&x]}else{0};(y,value)
                }).collect();
                let score=weights.values().copied().max().unwrap_or(0);
                if best.as_ref().is_none_or(|(s,v,_)|(score,x)<(*s,*v)){best=Some((score,x,weights));}
            }
            let (largest,v,weights)=best.ok_or(Error::Invalid("no centroid"))?;
            if 2*(largest as u128)>region.len() as u128{return Err(Error::Invalid("centroid bound"));}
            let Some(u)=self.classify(v,&weights)? else{return Ok((v,None));};
            if self.arrow(u,v)?{return Ok((v,Some(u)));}
            region=self.tree.component(u,Some(v),Some(&region),&mut self.work)?;
        }Err(Error::Invalid("lost central path/promise"))
    }
    fn arm(&mut self,mut prev:Node,mut v:Node,corners:&mut BTreeMap<Node,[Node;2]>)->Result<Vec<Node>,Error<E>> {
        let mut out=vec![];
        while !self.arrow(v,prev)? {self.work.tick()?;
            if corners.contains_key(&v){return Err(Error::Invalid("central path loop"));}
            let c=self.corner(v)?;if !c.contains(&prev){return Err(Error::Invalid("incoming central corner"));}
            corners.insert(v,c);out.push(v);let next=if c[0]==prev{c[1]}else{c[0]};prev=v;v=next;
        }Ok(out)
    }
    fn step(&mut self,z:u64)->Result<(),Error<E>> {
        if self.tree.taxa.contains(&Node::from(z)){return Err(Error::Invalid("duplicate inserted taxon"));}
        self.z=z;self.reps.clear();let (v,u)=self.central()?;
        if let Some(u)=u{self.tree.subdivide(v,u,z,&mut self.work)?;}
        else {
            let c=self.corner(v)?;let mut corners=BTreeMap::from([(v,c)]);
            let mut left=self.arm(v,c[0],&mut corners)?;let right=self.arm(v,c[1],&mut corners)?;
            left.reverse();left.push(v);left.extend(right);self.retired+=left.len();
            self.tree.merge_path(&left,&corners,z,&mut self.work)?;
        }Ok(())
    }
}
/// Same old adaptive order + sparse decoder, one original-label cache.
/// Only the complete exact circular binary-family promise justifies its output.
/// Every invalid/resource/oracle error aborts the whole request, never a prefix.
pub fn recover_unordered<E,F>(labels:&[u64],oracle:F,limits:OrderLimits)->Result<JointRecovery,Error<E>>
where F:FnMut(Quartet)->Result<u8,E> {
    if labels.len()<4{return Err(Error::Invalid("at least four taxa"));}
    if labels.len()>limits.search.taxa{return Err(Error::Unknown("taxon limit"));}
    let unique:BTreeSet<_>=labels.iter().copied().collect();
    if unique.len()!=labels.len(){return Err(Error::Invalid("distinct original labels"));}
    labels.len().checked_mul(2).ok_or(Error::Unknown("tree size overflow"))?;
    let mut shared=Shared{oracle,labels:unique,cache:BTreeMap::new(),trace:vec![],limit:limits.search.unique_queries};
    let mut learner=Learner{shared:&mut shared,tree:Tree::new(&labels[..3])?,
        work:Work{used:0,limit:limits.tree_work},reps:BTreeMap::new(),z:labels[3],
        predicates:0,predicate_limit:limits.search.predicates,centroids:0,retired:0};
    learner.tree.validate(&mut learner.work)?;
    for &z in &labels[3..]{learner.step(z)?;}
    let circle=learner.tree.one_order(&mut learner.work)?;
    let order_queries=learner.shared.cache.len();let predicates=learner.predicates;
    let centroids=learner.centroids;let retired=learner.retired;
    let internal=learner.tree.rot.len()-labels.len();let work=learner.work.used;
    drop(learner);
    let mut search_limits=limits.search;search_limits.predicates-=predicates;
    let mut recovery=super::recover(&circle,|q|shared.ask(q),search_limits)
        .map_err(|e|match e{Error::Invalid(x)=>Error::Invalid(x),Error::Unknown(x)=>Error::Unknown(x),Error::Oracle(e)=>e})?;
    let sparse_requests=recovery.cache.len();
    recovery.cache=shared.cache;recovery.query_trace=shared.trace;
    if retired!=labels.len()-2-internal{return Err(Error::Invalid("retired vertex accounting"));}
    Ok(JointRecovery{circle,recovery,order_queries,sparse_requests,order_predicates:predicates,
        centroid_steps:centroids,internal_vertices:internal,retired_vertices:retired,tree_work:work})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn support(circle:&[u64],splits:&[[usize;2]],q:Quartet)->u8 {
        let mut out=0;
        for &[a,b] in splits {
            let shore:Vec<_>=q.iter().filter(|x|{
                let i=circle.iter().position(|y|y==*x).unwrap();a<i&&i<=b
            }).copied().collect();
            if shore.len()==2{out|=pair_bit::<()>(q,[shore[0],shore[1]]).unwrap();}
        }out
    }
    #[test]
    fn existing_unknown_order_and_shared_decoder_match_retained_reference() {
        // Fixed new PORT/interface cases; no retained source/graph producer,
        // old main/grid/test runner, scientific model or controller is run.
        let mut cases=vec![];
        for n in [4usize,5,7,8,11,13] {
            let circle:Vec<_>=(0..n).map(|i|17+11*i as u64).collect();
            let mut labels=circle.clone();labels.reverse();labels.rotate_left(n/3);
            let chain:Vec<_>=(2..n-1).map(|j|[0,j]).collect();
            let dense:Vec<_>=(0..n).flat_map(|i|(i+2..n).map(move|j|[i,j]))
                .filter(|x|*x!=[0,n-1]).collect();
            cases.push((labels.clone(),circle.clone(),chain));
            cases.push((labels,circle,dense));
        }
        // Original numeric labels can exceed signed64; internal tree identities
        // must never truncate them or be exported as a taxon.
        let circle=vec![u64::MAX-9,8,700,u64::MAX-2,4,99];
        cases.push((vec![99,700,4,u64::MAX-2,8,u64::MAX-9],circle,vec![[0,2],[0,3],[0,4]]));
        let request:Vec<_>=cases.iter().map(|(labels,circle,splits)|
            serde_json::json!({"labels":labels,"circle":circle,"splits":splits})).collect();
        let program=r#"
import json,sys
sys.path.insert(0,sys.argv[1])
from recover_all import recover_all
from core import pair_bit
out=[]
for case in json.load(sys.stdin):
    circle=case["circle"];where={x:i for i,x in enumerate(circle)};calls=[]
    def oracle(q):
        calls.append(q);ans=0
        for a,b in case["splits"]:
            shore=[x for x in q if a<where[x]<=b]
            if len(shore)==2:ans |= pair_bit(q,shore)
        return ans
    r=recover_all(case["labels"],oracle)
    out.append({"circle":r.order,"splits":sorted(r.gap_pairs),
      "order_queries":r.order_queries,"total_queries":r.total_queries,
      "sparse_requests":r.sparse_requests,"internal":r.internal_vertices,
      "retired":r.retired_vertices,"trace":calls})
json.dump(out,sys.stdout)
"#;
        let reference=std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/exact-query-reference/order");
        let mut child=std::process::Command::new("python3").args(["-B","-c",program])
            .arg(reference).stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped()).env("PYTHONDONTWRITEBYTECODE","1")
            .spawn().expect("Python3 unchanged reference dependency");
        use std::io::Write;
        child.stdin.take().unwrap().write_all(serde_json::to_string(&request).unwrap().as_bytes()).unwrap();
        let output=child.wait_with_output().unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
        let expected:serde_json::Value=serde_json::from_slice(&output.stdout).unwrap();
        let mut retired=0;
        for ((labels,circle,splits),e) in cases.iter().zip(expected.as_array().unwrap()) {
            let r=recover_unordered(labels,|q|Ok::<_,()>(support(circle,splits,q)),OrderLimits::default()).unwrap();
            assert_eq!(serde_json::json!(r.circle),e["circle"]);
            assert_eq!(serde_json::json!(r.recovery.gap_pairs),e["splits"]);
            assert_eq!(serde_json::json!(r.order_queries),e["order_queries"]);
            assert_eq!(serde_json::json!(r.recovery.cache.len()),e["total_queries"]);
            assert_eq!(serde_json::json!(r.sparse_requests),e["sparse_requests"]);
            assert_eq!(serde_json::json!(r.internal_vertices),e["internal"]);
            assert_eq!(serde_json::json!(r.retired_vertices),e["retired"]);
            assert_eq!(serde_json::json!(r.recovery.query_trace.iter().map(|(q,_)|q).collect::<Vec<_>>()),e["trace"]);
            assert_eq!(r.recovery.cache.len(),r.recovery.query_trace.len());
            retired+=r.retired_vertices;
        }
        assert!(retired>0,"path-contraction branch must actually be covered");
    }
    #[test]
    fn order_limits_oracle_and_promise_failures_return_no_successful_prefix() {
        let labels=[40,10,30,20];
        let mut calls=0;
        let r=recover_unordered(&labels,|_|{calls+=1;Ok::<_,()>(1)},
            OrderLimits{tree_work:0,..OrderLimits::default()});
        assert_eq!(r,Err(Error::Unknown("order tree work limit")));assert_eq!(calls,0);
        let r=recover_unordered(&labels,|_|{calls+=1;Ok::<_,()>(1)},
            OrderLimits{search:Limits{unique_queries:0,..Limits::default()},..OrderLimits::default()});
        assert_eq!(r,Err(Error::Unknown("shared distinct quartet query limit")));assert_eq!(calls,0);
        assert_eq!(recover_unordered(&labels,|_|Err::<u8,_>("missing"),OrderLimits::default()),Err(Error::Oracle("missing")));
        assert_eq!(recover_unordered(&labels,|_|Ok::<_,()>(7),OrderLimits::default()),
            Err(Error::Invalid("nonempty circular binary support promise")));
        assert_eq!(recover_unordered(&[1,1,2,3],|_|Ok::<_,()>(1),OrderLimits::default()),
            Err(Error::Invalid("distinct original labels")));
    }
}

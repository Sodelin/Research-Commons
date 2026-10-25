//! NEW private decoder-only harness. Source-only; no execution acceptance.
//! Expected values are literal source-state fields, not a second decoder.
#[path="source_native_snapshot.rs"]
mod decode;
use decode::{DecodedLocation, Error};
use parity_solver::{forest::Tree, natural_cell::{Source, Edge, Hybrid},
    source_population::{Context, Snapshot, Location}, source_epoch::SelectedView};

const BIG:usize=9_007_199_254_740_993;
fn fork(sample:Vec<usize>,global_labels:Vec<usize>)->Context {
    assert!(usize::BITS>=64);
    Context {source:Source {vertices:3,root:0,
        edges:vec![Edge{source:0,target:1},Edge{source:0,target:2}],
        leaves:vec![1,2],hybrids:vec![]},sample,global_labels}
}
fn ordered(a:usize,b:usize)->Tree {
    Tree::Node(Box::new(Tree::Leaf(a)),Box::new(Tree::Leaf(b)))
}
fn carried()->Tree {Tree::Node(Box::new(ordered(0,1)),Box::new(Tree::Leaf(2)))}
fn role(p:&DecodedLocation)->(&'static str,usize) {match *p {
    DecodedLocation::Node(v)=>("NODE",v.index()),
    DecodedLocation::Edge(e)=>("EDGE",e.index()),
    DecodedLocation::RootPopulation(v)=>("ROOT_POPULATION",v.index()),
}}

#[test]
fn decoded_canonical_carry_defaults_full_fields() {
    let context=fork(vec![0;4],vec![BIG,0,17,1]);
    let input=Snapshot {live:vec![2,3],ancestor:vec![2,2,2,3],
        genealogy:vec![None,None,Some(carried()),Some(Tree::Leaf(3))],
        population:vec![None,None,Some(Location::Edge(0)),Some(Location::Edge(0))],
        register:vec![true,false,true]};
    let d=decode::decode_snapshot(&context,&input).unwrap();
    assert_eq!(d.live().iter().map(|x|x.index()).collect::<Vec<_>>(),vec![2,3]);
    assert_eq!(d.ancestor().iter().map(|x|x.index()).collect::<Vec<_>>(),vec![2,2,2,3]);
    // Dead defaults use each dead Copy, not its live ancestor or first leaf.
    assert_eq!(d.genealogy(),[Tree::Leaf(0),Tree::Leaf(1),carried(),Tree::Leaf(3)].as_slice());
    assert_eq!(d.location().iter().map(role).collect::<Vec<_>>(),
        vec![("NODE",0),("NODE",0),("EDGE",0),("EDGE",0)]);
    assert_eq!(d.register(),[true,false,true].as_slice());
    assert_eq!(d.context().global_labels,[BIG,0,17,1]);
    assert_eq!(d.source_event_history().len(),0);assert!(d.source_event_history().is_empty());
    let expected=SelectedView {genealogy:vec![Some(carried()),Some(carried()),Some(carried()),
        Some(Tree::Leaf(3))],population:vec![Some(Location::Edge(0));4],
        register:vec![true,false,true]};
    assert_eq!(d.full_selected(),&expected);
    // Ancillary roundtrip only AFTER exact decoded/selected field expectations.
    assert_eq!(d.canonical_snapshot(),input);
    assert!(matches!(d.original_parent_edge(0,true),Err(Error::OriginalHybridId)));
}

#[test]
fn decoded_original_role_occurrences_and_tampered_ranges() {
    let context=Context {source:Source {vertices:5,root:0,edges:vec![
        Edge{source:0,target:1},Edge{source:0,target:2},
        Edge{source:2,target:3},Edge{source:2,target:3},Edge{source:3,target:4}],
        leaves:vec![1,4],hybrids:vec![Hybrid{vertex:3,incoming:[2,3]}]},
        sample:vec![1,1],global_labels:vec![BIG,0]};
    let input=Snapshot {live:vec![1],ancestor:vec![1,1],
        genealogy:vec![None,Some(ordered(0,1))],
        population:vec![None,Some(Location::Edge(2))],register:vec![false,true,true,true,false]};
    let d=decode::decode_snapshot(&context,&input).unwrap();
    assert_eq!(d.live().iter().map(|x|x.index()).collect::<Vec<_>>(),vec![1]);
    assert_eq!(d.ancestor().iter().map(|x|x.index()).collect::<Vec<_>>(),vec![1,1]);
    assert_eq!(d.genealogy(),[Tree::Leaf(0),ordered(0,1)].as_slice());
    assert_eq!(d.location().iter().map(role).collect::<Vec<_>>(),vec![("NODE",0),("EDGE",2)]);
    assert_eq!(d.original_hybrid_vertex(0).unwrap().index(),3);
    assert_eq!(d.original_parent_edge(0,false).unwrap().index(),2);
    assert_eq!(d.original_parent_edge(0,true).unwrap().index(),3);
    assert_ne!(d.original_parent_edge(0,false).unwrap(),d.original_parent_edge(0,true).unwrap());
    assert_eq!(context.source.edges[2],context.source.edges[3]);
    let expected=SelectedView {genealogy:vec![Some(ordered(0,1)),Some(ordered(0,1))],
        population:vec![Some(Location::Edge(2));2],register:vec![false,true,true,true,false]};
    let r=decode::check_selected_range(&context,&input,&expected).unwrap();
    assert_eq!(r.selected(),&expected);assert_eq!(r.witness().canonical_snapshot(),input);
    let mut shifted_bit=expected.clone();shifted_bit.register[0]=true;shifted_bit.register[3]=false;
    assert!(matches!(decode::check_selected_range(&context,&input,&shifted_bit),
        Err(Error::SelectedRangeMismatch)),"hybrid ordinal0 is not original V3");
    let mut wrong_edge=expected.clone();wrong_edge.population=vec![Some(Location::Edge(3));2];
    assert!(matches!(decode::check_selected_range(&context,&input,&wrong_edge),
        Err(Error::SelectedRangeMismatch)),"parallel endpoints cannot erase E occurrence2/3");
    let mut wrong_graft=expected.clone();wrong_graft.genealogy=vec![Some(ordered(1,0));2];
    assert!(matches!(decode::check_selected_range(&context,&input,&wrong_graft),
        Err(Error::SelectedRangeMismatch)),"ordered children must survive decoding");
    let mut incomplete=expected.clone();incomplete.genealogy[0]=None;
    assert!(matches!(decode::check_selected_range(&context,&input,&incomplete),
        Err(Error::SelectedRangeMismatch)),"full Copy selection cannot omit one copy");
    let mut short=expected.clone();short.population.pop();
    assert!(matches!(decode::check_selected_range(&context,&input,&short),Err(Error::SelectedShape)));
    // A caller's wrong long tree is not cloned. The bounded expected tree
    // differs before traversal could follow the caller's full recursive depth.
    let mut deep=Tree::Leaf(0);for _ in 0..64 {deep=Tree::Node(Box::new(deep),Box::new(Tree::Leaf(1)));}
    let mut wrong_tree=expected.clone();wrong_tree.genealogy[0]=Some(deep);
    assert!(matches!(decode::check_selected_range(&context,&input,&wrong_tree),
        Err(Error::SelectedRangeMismatch)));
    assert_eq!(d.source_event_history().len(),0);
}

#[test]
fn decoded_empty_noncanonical_and_nonunique_ranges() {
    let context=fork(vec![0,0],vec![BIG,0]);
    let input=Snapshot {live:vec![0,1],ancestor:vec![0,1],
        genealogy:vec![Some(Tree::Leaf(0)),Some(Tree::Leaf(1))],
        population:vec![Some(Location::Ancestral(0)),Some(Location::Node(0))],
        register:vec![true,true,false]};
    let d=decode::decode_snapshot(&context,&input).unwrap();
    assert_eq!(d.location().iter().map(role).collect::<Vec<_>>(),
        vec![("ROOT_POPULATION",0),("NODE",0)]);
    assert_eq!(d.full_selected(),&SelectedView {genealogy:vec![Some(Tree::Leaf(0)),Some(Tree::Leaf(1))],
        population:vec![Some(Location::Ancestral(0)),Some(Location::Node(0))],
        register:vec![true,true,false]});
    let mut bad_root=input.clone();bad_root.population[0]=Some(Location::Ancestral(1));
    assert!(matches!(decode::decode_snapshot(&context,&bad_root),
        Err(Error::InvalidNativeSnapshot("SOURCE_LOCATION"))));
    let mut bad_ancestor=input.clone();bad_ancestor.ancestor[0]=usize::MAX;
    assert!(matches!(decode::decode_snapshot(&context,&bad_ancestor),
        Err(Error::InvalidNativeSnapshot("SOURCE_ANCESTOR"))));
    let mut active_none=input.clone();active_none.genealogy[0]=None;
    assert!(matches!(decode::decode_snapshot(&context,&active_none),
        Err(Error::InvalidNativeSnapshot("SOURCE_LIVE_GENEALOGY"))));

    // Valid canonical supplied ranges, not an assertion of natural reachability:
    // either representative can hold the SAME ordered tree and full selected view.
    let rep0=Snapshot {live:vec![0],ancestor:vec![0,0],genealogy:vec![Some(ordered(0,1)),None],
        population:vec![Some(Location::Ancestral(0)),None],register:vec![true,true,false]};
    let rep1=Snapshot {live:vec![1],ancestor:vec![1,1],genealogy:vec![None,Some(ordered(0,1))],
        population:vec![None,Some(Location::Ancestral(0))],register:vec![true,true,false]};
    let selected=SelectedView {genealogy:vec![Some(ordered(0,1)),Some(ordered(0,1))],
        population:vec![Some(Location::Ancestral(0));2],register:vec![true,true,false]};
    let r0=decode::check_selected_range(&context,&rep0,&selected).unwrap();
    let r1=decode::check_selected_range(&context,&rep1,&selected).unwrap();
    assert_eq!(r0.selected(),r1.selected());
    assert_ne!(r0.witness().canonical_snapshot(),r1.witness().canonical_snapshot());
    assert_eq!(r0.witness().live()[0].index(),0);assert_eq!(r1.witness().live()[0].index(),1);
    let mut dead_garbage=rep1.clone();dead_garbage.genealogy[0]=Some(Tree::Leaf(0));
    assert!(matches!(decode::decode_snapshot(&context,&dead_garbage),
        Err(Error::InvalidNativeSnapshot("SOURCE_CANONICAL_DEAD_FIELDS"))));

    let empty_context=fork(vec![],vec![]);
    let empty=Snapshot {live:vec![],ancestor:vec![],genealogy:vec![],population:vec![],
        register:vec![true,false,true]};
    let e=decode::decode_snapshot(&empty_context,&empty).unwrap();
    assert!(e.live().is_empty());assert!(e.ancestor().is_empty());
    assert!(e.genealogy().is_empty());assert!(e.location().is_empty());
    assert_eq!(e.register(),[true,false,true].as_slice());assert!(e.source_event_history().is_empty());
    assert_eq!(e.full_selected(),&SelectedView {genealogy:vec![],population:vec![],
        register:vec![true,false,true]});
    let mut oversized=empty_context.clone();oversized.source.vertices=usize::MAX;
    assert!(matches!(decode::decode_snapshot(&oversized,&empty),
        Err(Error::InvalidNativeSnapshot("SOURCE_POPULATION_CONTEXT"))));
}

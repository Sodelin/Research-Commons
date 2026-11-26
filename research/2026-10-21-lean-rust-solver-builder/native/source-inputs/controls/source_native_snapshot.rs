//! PRIVATE candidate: canonical native Snapshot -> decoded source-state image.
//! Value target: FiniteSourceSnapshot.decodeSnapshot (4628112b), with its
//! exact dead defaults and EMPTY SourceEvent history. This is not a native/Lean
//! refinement proof, a graph-class admission, or a literal Code-history decoder.
//! Validation/projection reuse the unchanged Context and full selected_view.
use parity_solver::{forest::Tree, source_epoch::{self as epoch, SelectedView},
    source_population::{Context, Location, Snapshot}};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CopyId(u8);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VertexId(u8);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EdgeId(u8);
impl CopyId { pub fn index(self) -> usize { usize::from(self.0) } }
impl VertexId { pub fn index(self) -> usize { usize::from(self.0) } }
impl EdgeId { pub fn index(self) -> usize { usize::from(self.0) } }

/// Constructor tags match the actual source Location. An original edge is an
/// OCCURRENCE, even if another edge has the same source/target pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodedLocation {
    Node(VertexId), Edge(EdgeId), RootPopulation(VertexId),
}
impl DecodedLocation {
    fn native(self) -> Location { match self {
        Self::Node(v) => Location::Node(v.index()),
        Self::Edge(e) => Location::Edge(e.index()),
        Self::RootPopulation(v) => Location::Ancestral(v.index()),
    } }
}

/// The typed snapshot decoder sets SourceEvent history to [], including for
/// noninitial snapshots. No events, merger ages or prefix records are recovered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmptySourceEventHistory(());
impl EmptySourceEventHistory {
    pub fn len(self) -> usize { 0 }
    pub fn is_empty(self) -> bool { true }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidNativeSnapshot(&'static str),
    SelectedShape,
    SelectedRangeMismatch,
    OriginalHybridId,
    Internal(&'static str),
}

fn copy_id(context: &Context, value: usize) -> Result<CopyId, Error> {
    if value >= context.sample.len() { return Err(Error::Internal("DECODE_COPY_RANGE")); }
    Ok(CopyId(u8::try_from(value).map_err(|_| Error::Internal("DECODE_COPY_WIDTH"))?))
}
fn vertex_id(context: &Context, value: usize) -> Result<VertexId, Error> {
    if value >= context.source.vertices { return Err(Error::Internal("DECODE_VERTEX_RANGE")); }
    Ok(VertexId(u8::try_from(value).map_err(|_| Error::Internal("DECODE_VERTEX_WIDTH"))?))
}
fn edge_id(context: &Context, value: usize) -> Result<EdgeId, Error> {
    if value >= context.source.edges.len() { return Err(Error::Internal("DECODE_EDGE_RANGE")); }
    Ok(EdgeId(u8::try_from(value).map_err(|_| Error::Internal("DECODE_EDGE_WIDTH"))?))
}
fn location(context: &Context, value: Location) -> Result<DecodedLocation, Error> {
    match value {
        Location::Node(v) => Ok(DecodedLocation::Node(vertex_id(context, v)?)),
        Location::Edge(e) => Ok(DecodedLocation::Edge(edge_id(context, e)?)),
        Location::Ancestral(v) => {
            if v != context.source.root { return Err(Error::Internal("DECODE_ROOT_POPULATION")); }
            Ok(DecodedLocation::RootPopulation(vertex_id(context, v)?))
        }
    }
}

/// Immutable, bounded image of a GIVEN validated native canonical snapshot.
/// Tree leaves use LOCAL Copy IDs, not the possibly large/permuted global labels.
/// Private fields prevent an unchecked decoded-state constructor or mutation.
/// The Context borrow fixes all original source/sample/global-label identities.
#[derive(Debug)]
pub struct DecodedSnapshot<'a> {
    context: &'a Context,
    live: Vec<CopyId>,
    ancestor: Vec<CopyId>,
    genealogy: Vec<Tree>,
    location: Vec<DecodedLocation>,
    register: Vec<bool>,
    selected: SelectedView,
    history: EmptySourceEventHistory,
}
impl<'a> DecodedSnapshot<'a> {
    pub fn context(&self) -> &'a Context { self.context }
    pub fn live(&self) -> &[CopyId] { &self.live }
    pub fn ancestor(&self) -> &[CopyId] { &self.ancestor }
    pub fn genealogy(&self) -> &[Tree] { &self.genealogy }
    pub fn location(&self) -> &[DecodedLocation] { &self.location }
    pub fn register(&self) -> &[bool] { &self.register }
    pub fn full_selected(&self) -> &SelectedView { &self.selected }
    pub fn source_event_history(&self) -> EmptySourceEventHistory { self.history }

    /// Native inverse on this canonical image only: live Some/dead None.
    /// This does not encode arbitrary typed Codes with dead garbage/active None.
    pub fn canonical_snapshot(&self) -> Snapshot {
        let live = self.live.iter().map(|id| id.index()).collect::<Vec<_>>();
        let genealogy = self.genealogy.iter().enumerate().map(|(i, tree)|
            if live.binary_search(&i).is_ok() { Some(tree.clone()) } else { None }).collect();
        let population = self.location.iter().enumerate().map(|(i, place)|
            if live.binary_search(&i).is_ok() { Some(place.native()) } else { None }).collect();
        Snapshot { live, ancestor: self.ancestor.iter().map(|id| id.index()).collect(),
            genealogy, population, register: self.register.clone() }
    }

    /// Original registry order is preserved. true selects incoming[1], whose
    /// original probability is Gamma; false selects incoming[0]. No coin is drawn.
    pub fn original_parent_edge(&self, hybrid: usize, parent_one: bool) -> Result<EdgeId, Error> {
        let h = self.context.source.hybrids.get(hybrid).ok_or(Error::OriginalHybridId)?;
        edge_id(self.context, h.incoming[usize::from(parent_one)])
    }
    pub fn original_hybrid_vertex(&self, hybrid: usize) -> Result<VertexId, Error> {
        let h = self.context.source.hybrids.get(hybrid).ok_or(Error::OriginalHybridId)?;
        vertex_id(self.context, h.vertex)
    }
}

/// Reuses selected_view's Context::validate_snapshot before cloning any tree.
/// Its existing bounds are Copy<=4 and graph counts<=32; iterative tree validation
/// rejects oversized/deep/repeated labels before the bounded recursive clones.
/// The domain is canonical encodeActual-like input, not every admitted typed Code.
pub fn decode_snapshot<'a>(context: &'a Context, input: &Snapshot)
    -> Result<DecodedSnapshot<'a>, Error> {
    let selected = epoch::selected_view(context, input).map_err(Error::InvalidNativeSnapshot)?;
    let root = vertex_id(context, context.source.root)?;
    let live = input.live.iter().map(|i| copy_id(context, *i)).collect::<Result<Vec<_>, _>>()?;
    let ancestor = input.ancestor.iter().map(|i| copy_id(context, *i)).collect::<Result<Vec<_>, _>>()?;
    let genealogy = input.genealogy.iter().enumerate().map(|(i, tree)|
        tree.as_ref().cloned().unwrap_or(Tree::Leaf(i))).collect();
    let locations = input.population.iter().map(|place| match place {
        Some(place) => location(context, *place),
        None => Ok(DecodedLocation::Node(root)),
    }).collect::<Result<Vec<_>, _>>()?;
    Ok(DecodedSnapshot { context, live, ancestor, genealogy, location: locations,
        register: input.register.clone(), selected, history: EmptySourceEventHistory(()) })
}

/// A supplied witness for one COMPLETE selected value, never its unique Code.
/// The snapshot may be a cached conditional range representative; acceptance
/// neither makes it a literal path endpoint nor proves conditional row equality.
#[derive(Debug)]
pub struct CheckedSelectedRange<'a> { witness: DecodedSnapshot<'a> }
impl<'a> CheckedSelectedRange<'a> {
    pub fn witness(&self) -> &DecodedSnapshot<'a> { &self.witness }
    pub fn selected(&self) -> &SelectedView { self.witness.full_selected() }
}

/// Validate the witness first. Claimed vectors must have exactly Copy/Copy/V
/// entries; equality then compares against already bounded trees, without cloning
/// caller trees or deriving live/ancestor fields from the Selected value.
pub fn check_selected_range<'a>(context: &'a Context, input: &Snapshot,
    claimed: &SelectedView) -> Result<CheckedSelectedRange<'a>, Error> {
    let witness = decode_snapshot(context, input)?;
    if claimed.genealogy.len() != context.sample.len()
        || claimed.population.len() != context.sample.len()
        || claimed.register.len() != context.source.vertices {
        return Err(Error::SelectedShape);
    }
    if witness.full_selected() != claimed { return Err(Error::SelectedRangeMismatch); }
    Ok(CheckedSelectedRange { witness })
}

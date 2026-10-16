//! UNCOMPILED SOURCE CANDIDATE, dot (OpenAI), 2026-10-16.
//! Additional CutChild check for the existing bounded Context representation.
//! Opt-in scientific admission only; leave the existing raw validation API unchanged.
//! This does not establish labelled planarity, outer-partner or physical-bank admission.
//! Intended consumer: parity_solver at 4e556c4ae6225d18fabf30bc7d3347a468749ebc.
use parity_solver::source_population::Context;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidContext(&'static str),
    NonBridgeHybridChild { original_edge: usize },
}

/// Each adjacency entry retains its ORIGINAL edge occurrence ID.
type Adjacency = Vec<Vec<(usize, usize)>>;

/// Preconditions: start/target and every adjacency neighbor are in range.
/// Only the exact removed edge ID is skipped; equal endpoint pairs survive.
fn reaches_without(adjacency: &Adjacency, removed: usize,
    start: usize, target: usize) -> bool {
    let mut seen = vec![false; adjacency.len()];
    let mut stack = vec![start];
    seen[start] = true;
    while let Some(vertex) = stack.pop() {
        if vertex == target { return true; }
        for &(neighbor, edge_id) in &adjacency[vertex] {
            if edge_id != removed && !seen[neighbor] {
                seen[neighbor] = true;
                stack.push(neighbor);
            }
        }
    }
    false
}

/// Successful return adds exactly CutChild to existing Context validation.
/// It does not mutate the Context, registry ordering, labels, or parameter data.
pub fn check_cut_child(context: &Context) -> Result<(), Error> {
    context.validate().map_err(Error::InvalidContext)?;
    let source = &context.source;
    let mut adjacency: Adjacency = vec![Vec::new(); source.vertices];
    for (edge_id, edge) in source.edges.iter().enumerate() {
        adjacency[edge.source].push((edge.target, edge_id));
        adjacency[edge.target].push((edge.source, edge_id));
    }
    let mut is_hybrid = vec![false; source.vertices];
    for hybrid in &source.hybrids { is_hybrid[hybrid.vertex] = true; }
    for (edge_id, edge) in source.edges.iter().enumerate() {
        if is_hybrid[edge.source]
            && reaches_without(&adjacency, edge_id, edge.source, edge.target) {
            return Err(Error::NonBridgeHybridChild { original_edge: edge_id });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use parity_solver::natural_cell::{Source, Edge, Hybrid};

    fn context(vertices: usize, pairs: &[(usize, usize)], leaves: &[usize],
        hybrids: &[(usize, [usize; 2])]) -> Context {
        Context {
            source: Source { vertices, root: 0,
                edges: pairs.iter().map(|&(source,target)| Edge { source,target }).collect(),
                leaves: leaves.to_vec(),
                hybrids: hybrids.iter().map(|&(vertex,incoming)| Hybrid { vertex,incoming }).collect(),
            },
            sample: (0..leaves.len()).collect(),
            global_labels: (0..leaves.len()).collect(),
        }
    }

    fn adjacency(vertices: usize, pairs: &[(usize, usize)]) -> Adjacency {
        let mut result = vec![Vec::new(); vertices];
        for (id, &(a,b)) in pairs.iter().enumerate() {
            result[a].push((b,id)); result[b].push((a,id));
        }
        result
    }

    #[test]
    fn published_four_taxon_counterexample_is_rejected() {
        let c = context(11,
            &[(0,1),(0,2),(1,3),(1,6),(2,3),(2,4),
              (3,5),(4,5),(4,9),(5,10),(6,7),(6,8)],
            &[7,8,9,10], &[(3,[2,4]),(5,[6,7])]);
        assert_eq!(c.validate(), Ok(()));
        assert_eq!(check_cut_child(&c),
            Err(Error::NonBridgeHybridChild { original_edge: 6 }));
    }

    #[test]
    fn parallel_parent_occurrences_with_bridge_child_are_accepted() {
        let c = context(9,
            &[(0,1),(0,3),(1,2),(1,2),(2,4),(3,5),(3,6),(4,7),(4,8)],
            &[5,6,7,8], &[(2,[2,3])]);
        assert_eq!(c.validate(), Ok(()));
        assert_eq!(check_cut_child(&c), Ok(()));
    }

    #[test]
    fn parallel_edge_deletion_does_not_delete_its_partner() {
        let a = adjacency(2, &[(0,1),(0,1)]);
        assert!(reaches_without(&a, 0, 0, 1));
        assert!(reaches_without(&a, 1, 0, 1));
    }

    #[test]
    fn single_edge_disconnects() {
        assert!(!reaches_without(&adjacency(2, &[(0,1)]), 0, 0, 1));
    }

    #[test]
    fn triangle_detour_survives() {
        assert!(reaches_without(&adjacency(3, &[(0,1),(1,2),(2,0)]), 0, 0, 1));
    }

    #[test]
    fn loop_has_reflexive_detour() {
        // A low-level helper control; Source::validate excludes this directed cycle.
        assert!(reaches_without(&adjacency(1, &[(0,0)]), 0, 0, 0));
    }

    #[test]
    fn hybrid_free_source_is_vacuously_cut_child() {
        let c = context(3, &[(0,1),(0,2)], &[1,2], &[]);
        assert_eq!(check_cut_child(&c), Ok(()));
    }

    #[test]
    fn malformed_context_is_rejected_before_adjacency_indexing() {
        let c = context(3, &[(0,1),(0,99)], &[1,2], &[]);
        assert!(matches!(check_cut_child(&c), Err(Error::InvalidContext(_))));
    }
}

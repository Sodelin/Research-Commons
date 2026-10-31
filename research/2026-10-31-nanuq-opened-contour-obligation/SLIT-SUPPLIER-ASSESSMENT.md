# Qualified slit / bridge-face supplier inspection

Status: read-only source assessment, not a new theorem or impossibility claim. Scope is the exact qualified128 closure rooted at Schoenflies.JordanSchoenflies, upstream05a43d29cde026618777db3d4e4316204ccca237.

Available exact APIs:
- `SkeletonAccess.IsLocalRadius.ball_diff_eq_slit` identifies a disk minus the set with a disk minus a radial segment, assuming IsLocalRadius and a singleton localDirs set.
- `SkeletonAccess.IsLocalRadius.isConnected_ball_diff_of_subsingleton` proves connectedness of that local complement, assuming IsLocalRadius and subsingleton localDirs. Neither supplies the local-radius premise for the given continuous source drawing.
- `Graph.IsDrawing.exists_unbounded_face` and `Graph.unbounded_face_unique` in Graph.OuterFace apply to any finite IsDrawing. They do not exclude additional bounded faces or supply a contour/order.
- `Graph.face_union_eq_of_disjoint` in FaceCycles preserves a face missed by an added graph. It is not a face-merger theorem for deletion.
- SourceJoining concerns generated polygonal grid/crosscut carriers; its endpoint/overlay hypotheses are not the desired generic dangling-arc deletion statement.
- ArcComplement proves single-arc complement results; combinatorial Graph.Tree does not by itself furnish finite-tree drawing nonseparation.
- Existing crosscut theorems put BOTH endpoints on a Jordan boundary. A slit with one endpoint interior and only one boundary endpoint does not satisfy that statement merely by renaming variables.

No ready theorem was identified in this inspected closure for: deleting/truncating an original dangling continuous arc, exact merging of its incident faces, or connected complement of an arbitrary actual finite embedded tree. This is a bounded source-search outcome, not a claim of global library nonexistence.

A source-specific route may be enough: an interior point of a removed original arc segment is separated from all other retained compact edge traces; an open neighborhood in the new complement can merge old faces incident with the removed segment. However, deriving the exact incident-face list, exhausting all relevant old faces, and tracing the resulting opened contour with adjacent duplicate blocks and collapse to original C are still proof obligations. No component-merger or nonseparation theorem is claimed established here.

The original same-drawing face-cycle route is retained as a useful provider, including actual bigons, rather than discarded in favor of an unproved general-tree shortcut. No supplier execution, installation, archive transfer or held-audit retry occurred.

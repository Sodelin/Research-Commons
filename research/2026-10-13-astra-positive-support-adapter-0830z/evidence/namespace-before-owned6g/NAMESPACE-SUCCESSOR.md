# Owned namespace routing successor — source only

Lean selects an import namespace root before checking the complete requested
module path. The original unexecuted owned builder prepended a partial Mathlib
directory, which would mask the rest of the authenticated external Mathlib tree.
The official source rule and observed source-query failure are preserved in
`evidence/NAMESPACE-RESOLUTION-PREBUILD-FINDING.json` and the separate query2355
packet. No historical owned compiler failure is invented.

The new `build_support_namespace.py` retains the exact selected statements and
external3591 graph. It authenticates every external source, receipt, log and
object, checks namespace routing for the complete external graph, then puts
those complete external namespaces before the owned research/Astra library.
Every earlier top namespace directory or root object for a selected non-Mathlib
owned module causes refusal. Exact selected source and object identities bind
the seven owned Mathlib modules to their actual external providers; copied owned
objects remain authenticated reuse and are explicitly not the selected imports.

`NAMESPACE-RESOLUTION.json`, the owned plan, every module receipt and the final
interface audit bind the route, controlled environment and compiler options.
Resume also checks the actual compiler command and helper identity. Existing
unreceipted-file rejection and axiom/placeholder checks remain in force. A fresh
owned state is required; old plans and failed outputs must not be overwritten.

The matching target is `lake -f lakefile.namespace.lean build adapter`. Its
separate interface compiler and `capture_final_namespace.py` authenticate the
same routing. The predecessor builder, Lake file, audit and capture remain
unchanged as historical sources. Provider/final guards retain their existing
5 GiB virtual / 4 GiB physical profile; the external builder's separately
reviewed 6 GiB virtual profile is not silently inherited.

All new files are currently source-only. Nine synthetic namespace controls and
seven inherited final-evidence gate controls are prepared but not executed.
They do not simulate theorem compilation. After source review, run those bounded
controls at a quiet boundary, then one fresh accepted source after the entire
external closure is authenticated. Actual provider/adapter compilation, explicit
type and axiom audits, Lake execution, final capture and remote publication are
still required. Nothing here supplies the missing protected physical provider.

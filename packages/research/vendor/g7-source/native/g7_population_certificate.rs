//! Bounded SOURCE-ONLY exporter for the existing population Table.
//! No population engine, process, compiler, parser, network or record writer.
//! The resulting Lean source is a proposal until its complete context checks.
#![forbid(unsafe_code)]

use parity_solver::{q, Rational};
use parity_solver::forest::Tree;
use parity_solver::source_population::{Context, Location, Snapshot, Table};

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub destinations: usize,
    pub monomials: usize,
    pub rational_bits: u64,
    pub rendered_bytes: usize,
    pub name_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { destinations: 4096, monomials: 65536, rational_bits: 65536,
            rendered_bytes: 4 * 1024 * 1024, name_bytes: 512 }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    Unknown { kind: &'static str, required: Option<usize>, cap: usize },
}
type Result<T> = std::result::Result<T, Error>;

/// Existing original RootedBinary value in a supplied Lean context. The emitted
/// source CHECKS its exact Fin carriers, root, edge occurrences and taxon order.
/// Names contain only checked identifier segments; no Lean source is accepted.
#[derive(Clone, Copy, Debug)]
pub struct Bindings<'a> {
    pub original_module: &'a str,
    pub original_source: &'a str,
    pub namespace: &'a str,
}

/// In-process association with ALL literal native inputs, not runtime origin,
/// a passed Lean result, scientific source admission or a selected programme.
#[derive(Debug)]
pub struct Prepared<'a> {
    context: &'a Context,
    entering: &'a Snapshot,
    table: &'a Table,
    bindings: Bindings<'a>,
    document: String,
}
impl<'a> Prepared<'a> {
    pub fn context(&self) -> &'a Context { self.context }
    pub fn entering(&self) -> &'a Snapshot { self.entering }
    pub fn table(&self) -> &'a Table { self.table }
    pub fn bindings(&self) -> Bindings<'a> { self.bindings }
    pub fn document(&self) -> &str { &self.document }
}

fn unknown(kind: &'static str, required: Option<usize>, cap: usize) -> Error {
    Error::Unknown { kind, required, cap }
}
fn name(value: &str, limit: usize) -> Result<()> {
    if value.is_empty() { return Err(Error::Invalid("POP_CERT_NAME_LENGTH")); }
    if value.len() > limit { return Err(unknown("name_bytes", Some(value.len()), limit)); }
    for part in value.split('.') {
        if matches!(part, "_" | "sorry" | "admit" | "by" | "axiom" | "opaque"
            | "unsafe" | "def" | "abbrev" | "theorem" | "lemma" | "example"
            | "import" | "namespace" | "end" | "open" | "export" | "run_cmd"
            | "set_option" | "where" | "with" | "match" | "if" | "then" | "else"
            | "fun" | "forall" | "Type" | "Prop" | "Sort" | "true" | "false") {
            return Err(Error::Invalid("POP_CERT_RESERVED_NAME"));
        }
        let mut bytes = part.bytes();
        let first = bytes.next().ok_or(Error::Invalid("POP_CERT_NAME_SEGMENT"))?;
        if !(first.is_ascii_alphabetic() || first == b'_')
            || bytes.any(|b| !(b.is_ascii_alphanumeric() || b == b'_' || b == 39)) {
            return Err(Error::Invalid("POP_CERT_NAME_SYNTAX"));
        }
    }
    Ok(())
}
fn rational(value: &Rational, limits: Limits) -> Result<()> {
    if value.denom() <= q(0,1).numer() {
        return Err(Error::Invalid("POP_CERT_DENOMINATOR"));
    }
    let bits = value.numer().bits().max(value.denom().bits());
    if bits > limits.rational_bits {
        return Err(unknown("rational_bits", usize::try_from(bits).ok(),
            usize::try_from(limits.rational_bits).unwrap_or(usize::MAX)));
    }
    let normalized = Rational::new(value.numer().clone(), value.denom().clone());
    if normalized.numer() != value.numer() || normalized.denom() != value.denom() {
        return Err(Error::Invalid("POP_CERT_NONCANONICAL_RATIONAL"));
    }
    Ok(())
}
fn preflight(context: &Context, entering: &Snapshot, table: &Table,
    bindings: Bindings<'_>, limits: Limits) -> Result<()> {
    name(bindings.original_module, limits.name_bytes)?;
    name(bindings.original_source, limits.name_bytes)?;
    name(bindings.namespace, limits.name_bytes)?;
    for (kind, required, cap) in [
        ("inherited_vertices", context.source.vertices, 32),
        ("inherited_edges", context.source.edges.len(), 32),
        ("inherited_taxa", context.source.leaves.len(), 32),
        ("inherited_hybrids", context.source.hybrids.len(), 32),
        ("inherited_copies", context.sample.len(), 4),
    ] {
        if required > cap { return Err(unknown(kind, Some(required), cap)); }
    }
    let bank = context.source.dimension();
    if bank > 32 { return Err(unknown("inherited_full_bank", Some(bank), 32)); }
    context.validate_snapshot(entering).map_err(Error::Invalid)?;
    match table.population {
        Location::Edge(e) if e < context.source.edges.len() => (),
        Location::Ancestral(v) if v == context.source.root => (),
        _ => return Err(Error::Invalid("POP_CERT_ORIGINAL_POPULATION")),
    }
    if entering.live.iter().any(|i| entering.population[*i] != Some(table.population)) {
        return Err(Error::Invalid("POP_CERT_NOT_COLOCATED"));
    }
    if table.transitions.len() > limits.destinations {
        return Err(unknown("destinations", Some(table.transitions.len()), limits.destinations));
    }
    let mut monomials = 0usize;
    for transition in &table.transitions {
        context.validate_snapshot(&transition.destination).map_err(Error::Invalid)?;
        if transition.destination.register != entering.register {
            return Err(Error::Invalid("POP_CERT_REGISTER_CHANGED"));
        }
        let polynomial = &transition.polynomial;
        if polynomial.dimension != 1 {
            return Err(Error::Invalid("POP_CERT_UNIVARIATE_DIMENSION"));
        }
        monomials = monomials.checked_add(polynomial.terms.len())
            .ok_or_else(|| unknown("monomials", None, limits.monomials))?;
        if monomials > limits.monomials {
            return Err(unknown("monomials", Some(monomials), limits.monomials));
        }
        for (powers, coefficient) in &polynomial.terms {
            // Preserve every literal exponent. The finite checker catches a
            // foreign nonzero degree; the exporter does not expand powers.
            if powers.len() != 1 {
                return Err(Error::Invalid("POP_CERT_EXPONENT_ARITY"));
            }
            rational(coefficient, limits)?;
        }
    }
    Ok(())
}

struct Writer { text: String, cap: usize }
impl Writer {
    fn new(cap: usize) -> Self { Self { text: String::new(), cap } }
    fn put(&mut self, value: &str) -> Result<()> {
        let next = self.text.len().checked_add(value.len())
            .ok_or_else(|| unknown("rendered_bytes", None, self.cap))?;
        if next > self.cap { return Err(unknown("rendered_bytes", Some(next), self.cap)); }
        self.text.try_reserve(value.len())
            .map_err(|_| unknown("rendered_allocation", Some(next), self.cap))?;
        self.text.push_str(value);
        Ok(())
    }
    fn number(&mut self, value: usize) -> Result<()> { self.put(&value.to_string()) }
}
fn fin(out: &mut Writer, value: usize) -> Result<()> {
    out.put("⟨")?; out.number(value)?; out.put(", by decide⟩")
}
fn function<F>(out: &mut Writer, length: usize, mut value: F) -> Result<()>
where F: FnMut(&mut Writer, usize) -> Result<()> {
    if length == 0 { return out.put("(fun i => Fin.elim0 i)"); }
    out.put("(fun i => ")?;
    for i in 0..length-1 {
        out.put("if i.val = ")?; out.number(i)?; out.put(" then ")?;
        value(out,i)?;
        out.put(" else ")?;
    }
    value(out,length-1)?;
    out.put(")")
}
fn tree(out: &mut Writer, value: &Tree) -> Result<()> {
    match value {
        Tree::Leaf(i) => { out.put("(.leaf ")?; fin(out,*i)?; out.put(")") }
        Tree::Node(a,b) => {
            out.put("(.graft ")?; tree(out,a)?; out.put(" ")?;
            tree(out,b)?; out.put(")")
        }
    }
}
fn location(out: &mut Writer, value: Location) -> Result<()> {
    match value {
        Location::Node(v) => { out.put("(.node ")?; fin(out,v)?; out.put(")") }
        Location::Edge(e) => { out.put("(.edge ")?; fin(out,e)?; out.put(")") }
        Location::Ancestral(v) => {
            out.put("(.rootPopulation ")?; fin(out,v)?; out.put(")")
        }
    }
}
fn snapshot(out: &mut Writer, label: &str, context: &Context, value: &Snapshot) -> Result<()> {
    out.put("private def ")?; out.put(label)?;
    out.put("Snapshot : Snapshot (Fin ")?; out.number(context.source.vertices)?;
    out.put(") (Fin ")?; out.number(context.source.edges.len())?;
    out.put(") (Fin ")?; out.number(context.sample.len())?; out.put(") where\n  live := ")?;
    if value.live.is_empty() { out.put("∅")?; }
    else {
        out.put("{")?;
        for (i,copy) in value.live.iter().enumerate() {
            if i != 0 { out.put(", ")?; }
            fin(out,*copy)?;
        }
        out.put("}")?;
    }
    out.put("\n  ancestor := ")?;
    function(out,context.sample.len(),|out,i| fin(out,value.ancestor[i]))?;
    out.put("\n  genealogy := ")?;
    function(out,context.sample.len(),|out,i| match &value.genealogy[i] {
        None => out.put("none"),
        Some(t) => { out.put("(some ⟨")?; tree(out,t)?; out.put(", by decide⟩)") }
    })?;
    out.put("\n  population := ")?;
    function(out,context.sample.len(),|out,i| match value.population[i] {
        None => out.put("none"),
        Some(p) => { out.put("(some ")?; location(out,p)?; out.put(")") }
    })?;
    out.put("\n  register := ")?;
    function(out,context.source.vertices,|out,i| out.put(if value.register[i] {"true"} else {"false"}))?;
    out.put("\n\nprivate def ")?; out.put(label)?; out.put(" : Code N sample :=\n  ⟨")?;
    out.put(label)?; out.put("Snapshot, by\n    change SourceValid N sample (decode N.root ")?;
    out.put(label)?; out.put("Snapshot)\n    letI := sourceValidDecidable N sample (decode N.root ")?;
    out.put(label)?; out.put("Snapshot)\n    decide⟩\n\n")
}
fn expression(out: &mut Writer, polynomial: &parity_solver::polynomial::Polynomial) -> Result<()> {
    out.put("[")?;
    for (i,(powers,coefficient)) in polynomial.terms.iter().enumerate() {
        if i != 0 { out.put(", ")?; }
        out.put("(")?; out.number(powers[0])?;
        out.put(", ((")?; out.put(&coefficient.numer().to_string())?;
        out.put(" : ℚ) / (")?; out.put(&coefficient.denom().to_string())?;
        out.put(" : ℚ)))")?;
    }
    out.put("]")
}

/// Render a complete candidate source in RAM. This does NOT invoke Lean or the
/// native engine and does not call the resulting source a checked certificate.
/// Exact named-context/import installation and actual kernel checking remain
/// required; any failed proof target refuses the entire candidate.
pub fn prepare<'a>(context: &'a Context, entering: &'a Snapshot, table: &'a Table,
    bindings: Bindings<'a>, limits: Limits) -> Result<Prepared<'a>> {
    preflight(context,entering,table,bindings,limits)?;
    let mut out = Writer::new(limits.rendered_bytes);
    out.put("import NativePopulationTableCertificate\nimport ")?;
    out.put(bindings.original_module)?; out.put("\n\n")?;
    out.put("-- SOURCE CANDIDATE; checking/imports/runtime origin are not supplied.\n")?;
    out.put("namespace ")?; out.put(bindings.namespace)?;
    out.put("\nopen Nanuq.Source GProgram.SourceForest\n")?;
    out.put("open UnifiedLean.Source.FiniteSourceSnapshot\n")?;
    out.put("open UnifiedLean.Source.UniformizedSourceStep\n")?;
    out.put("open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel\n")?;
    out.put("open GProgram.G7.EffectiveSourceEnumeration\n")?;
    out.put("open GProgram.G7.EffectivePopulationCoefficients\n")?;
    out.put("open GProgram.G7.SinglePopulationPolynomialKernel\nopen scoped NNReal\n")?;
    out.put("open Astra.NativePopulationTableCertificate\n\n")?;
    context_declarations_into(&mut out,context,bindings)?;
    snapshot(&mut out,"entering",context,entering)?;
    for (i,transition) in table.transitions.iter().enumerate() {
        snapshot(&mut out,&format!("destination{i}"),context,&transition.destination)?;
    }
    out.put("private def rows : Table N sample := [")?;
    for (i,transition) in table.transitions.iter().enumerate() {
        if i != 0 { out.put(",\n  ")?; }
        out.put("(destination")?; out.number(i)?; out.put(", ")?;
        expression(&mut out,&transition.polynomial)?; out.put(")")?;
    }
    out.put("]\n\nprivate def population : Option (Fin ")?;
    out.number(context.source.edges.len())?; out.put(") := ")?;
    match table.population {
        Location::Edge(e) => { out.put("(some ")?; fin(&mut out,e)?; out.put(")")?; }
        Location::Ancestral(_) => out.put("none")?,
        Location::Node(_) => return Err(Error::Invalid("POP_CERT_ORIGINAL_POPULATION")),
    }
    out.put("\n\ntheorem entering_colocated : CoLocated N entering population := by decide\n")?;
    out.put("\ntheorem coefficient_table_checked : check N ")?;
    out.number(context.sample.len())?; out.put(" entering rows = true := by decide\n\n")?;
    out.put("theorem original_population_probability (d : Code N sample)\n")?;
    out.put("    (r : PositivePairRates (Fin ")?; out.number(context.source.edges.len())?;
    out.put(")) (t : ℝ≥0) :\n")?;
    out.put("    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r population * (t : ℝ)))\n")?;
    out.put("      (exprPolynomial (collect rows d)) = (sourceTimeKernel N r t entering d).toReal := by\n")?;
    out.put("  exact checked_actual_population N entering rows\n")?;
    out.put("    (by simpa using coefficient_table_checked) d population entering_colocated r t\n\nend ")?;
    out.put(bindings.namespace)?; out.put("\n")?;
    Ok(Prepared { context, entering, table, bindings, document: out.text })
}

// Portable integration variant: expose the EXISTING literal renderers so the
// full epoch caller need not duplicate the context/snapshot format. These
// functions do no engine work or I/O and return unaccepted source in RAM.
fn context_declarations_into(out: &mut Writer, context: &Context, bindings: Bindings<'_>) -> Result<()> {
    out.put("private abbrev N : RootedBinary (Fin ")?; out.number(context.source.vertices)?;
    out.put(") (Fin ")?; out.number(context.source.edges.len())?;
    out.put(") (Fin ")?; out.number(context.source.leaves.len())?; out.put(") := ")?;
    out.put(bindings.original_source)?; out.put("\n\nprivate def sample : Fin ")?;
    out.number(context.sample.len())?; out.put(" → Fin ")?;
    out.number(context.source.leaves.len())?; out.put(" := ")?;
    function(out,context.sample.len(),|out,i| fin(out,context.sample[i]))?;
    out.put("\n\ntheorem root_exact : N.root = ")?; fin(out,context.source.root)?;
    out.put(" := by decide\n\ntheorem edge_sources_exact : N.graph.source = ")?;
    function(out,context.source.edges.len(),|out,i| fin(out,context.source.edges[i].source))?;
    out.put(" := by decide\n\ntheorem edge_targets_exact : N.graph.target = ")?;
    function(out,context.source.edges.len(),|out,i| fin(out,context.source.edges[i].target))?;
    out.put(" := by decide\n\ntheorem taxa_exact : N.leaf = ")?;
    function(out,context.source.leaves.len(),|out,i| fin(out,context.source.leaves[i]))?;
    out.put(" := by decide\n\n")?;
    Ok(())
}
pub fn render_context_declarations(context: &Context, bindings: Bindings<'_>, limits: Limits) -> Result<String> {
    context.validate().map_err(Error::Invalid)?;
    name(bindings.original_module, limits.name_bytes)?;
    name(bindings.original_source, limits.name_bytes)?;
    name(bindings.namespace, limits.name_bytes)?;
    let mut out = Writer::new(limits.rendered_bytes);
    context_declarations_into(&mut out, context, bindings)?;
    Ok(out.text)
}
pub fn render_snapshot_declarations(context: &Context, value: &Snapshot, label: &str, limits: Limits) -> Result<String> {
    name(label, limits.name_bytes)?;
    context.validate_snapshot(value).map_err(Error::Invalid)?;
    let mut out = Writer::new(limits.rendered_bytes);
    snapshot(&mut out, label, context, value)?;
    Ok(out.text)
}

/// Render the existing full selected view of an ACTUALLY validated witness.
/// This is literal projection formatting, not a stochastic transition engine.
pub fn render_selected_view_declarations(context: &Context, value: &Snapshot, label: &str, limits: Limits) -> Result<String> {
    name(label, limits.name_bytes)?;
    let view = parity_solver::source_epoch::selected_view(context, value).map_err(Error::Invalid)?;
    let mut out = Writer::new(limits.rendered_bytes);
    out.put("private def ")?; out.put(label)?;
    out.put("View : SelectedView (Fin ")?; out.number(context.source.vertices)?;
    out.put(") (Fin ")?; out.number(context.source.edges.len())?;
    out.put(") (Fin ")?; out.number(context.sample.len())?; out.put(") where\n  genealogy := ")?;
    function(&mut out, context.sample.len(), |out,i| match &view.genealogy[i] {
        None => out.put("none"),
        Some(t) => { out.put("(some ")?; tree(out,t)?; out.put(")") }
    })?;
    out.put("\n  population := ")?;
    function(&mut out, context.sample.len(), |out,i| match view.population[i] {
        None => out.put("none"),
        Some(p) => { out.put("(some ")?; location(out,p)?; out.put(")") }
    })?;
    out.put("\n  register := ")?;
    function(&mut out, context.source.vertices, |out,i| out.put(if view.register[i] {"true"} else {"false"}))?;
    out.put("\n\n")?;
    Ok(out.text)
}

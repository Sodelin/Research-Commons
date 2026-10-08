"""Versioned molecular contracts. Coordinates are always explicit.

This experimental interface carries model predictions, never measured RNA or
an established biological conclusion. It has no dependency on an SDK.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
import math
from typing import Any

CONTRACT_VERSION = "molecular-apps-v1"
STATUSES = frozenset({"SUCCESS", "INVALID_INPUT", "UNSUPPORTED", "UNKNOWN", "RESOURCE_LIMIT", "EXECUTION_FAILURE"})
OUTPUT_TYPES = frozenset({"RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE", "SPLICE_JUNCTIONS", "ATAC"})
FAMILIES = frozenset({"expression", "splice_sites", "splice_usage", "splice_junctions", "polyadenylation"})


class MolecularError(Exception):
    def __init__(self, status: str, code: str, message: str):
        if status not in STATUSES:
            raise ValueError("invalid status")
        super().__init__(message)
        self.status, self.code, self.message = status, code, message

    def to_result(self) -> dict:
        return {"contract_version": CONTRACT_VERSION, "status": self.status,
                "code": self.code, "message": self.message,
                "successful_computation": False, "biological_conclusion_established": False}


def require(condition: bool, code: str, message: str, status: str = "INVALID_INPUT") -> None:
    if not condition:
        raise MolecularError(status, code, message)


def sequence_sha256(sequence: str) -> str:
    return hashlib.sha256(sequence.encode("ascii")).hexdigest()


def identity_sha256(value: Any) -> str:
    if hasattr(value, "__dataclass_fields__"):
        value = asdict(value)
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def _text(value: Any, name: str) -> None:
    require(isinstance(value, str) and bool(value) and not any(ord(c) < 32 for c in value), "TEXT", f"{name} must be nonempty text without control characters")


def _integer(value: Any, name: str) -> None:
    require(type(value) is int, "COORDINATE", f"{name} must be an integer")


def _finite_number(value: Any) -> bool:
    if type(value) not in {int, float}:
        return False
    try:
        return math.isfinite(value)
    except OverflowError:
        return False


@dataclass(frozen=True)
class ReferenceWindow:
    assembly: str
    chromosome: str
    start0: int
    sequence: str
    guard_sequence: str
    source: str
    sha256: str

    @property
    def end0(self) -> int:
        return self.start0 + len(self.sequence)

    def validate(self) -> None:
        require(self.assembly in {"GRCh38", "GRCh38.p13", "hg38"}, "ASSEMBLY", "initial human module supports GRCh38/hg38 only", "UNSUPPORTED")
        _text(self.chromosome, "chromosome"); _integer(self.start0, "start0")
        require(self.start0 >= 0, "COORDINATE", "negative reference start")
        require(isinstance(self.sequence, str) and 0 < len(self.sequence) <= 2**20, "WINDOW", "reference sequence length must be 1..1048576")
        require(isinstance(self.guard_sequence, str) and len(self.guard_sequence) <= 2**20, "GUARD", "guard sequence exceeds limit")
        require(set(self.sequence + self.guard_sequence) <= set("ACGTN"), "SEQUENCE", "reference and guard must be uppercase ACGTN")
        _text(self.source, "reference source")
        require(self.sha256 == sequence_sha256(self.sequence + self.guard_sequence), "REFERENCE_HASH", "reference+guard SHA256 mismatch")


@dataclass(frozen=True)
class TranscriptAnnotation:
    gene_id: str
    transcript_id: str
    start0: int
    end0: int
    strand: str
    source: str
    version: str
    exons: tuple[tuple[int, int], ...]

    def validate(self, window: ReferenceWindow) -> None:
        for k in ("gene_id", "transcript_id", "source", "version"):
            _text(getattr(self, k), k)
        _integer(self.start0, "transcript_start0"); _integer(self.end0, "transcript_end0")
        require(window.start0 <= self.start0 < self.end0 <= window.end0, "TRANSCRIPT_WINDOW", "complete transcript must be within the reference window")
        require(self.strand in {"+", "-"}, "STRAND", "transcript strand must be + or -")
        require(bool(self.exons), "ANNOTATION", "at least one explicit exon is required")
        previous = self.start0
        for start, end in self.exons:
            _integer(start, "exon start"); _integer(end, "exon end")
            require(previous <= start < end <= self.end0, "EXON", "exons must be sorted, disjoint and within the transcript")
            previous = end


@dataclass(frozen=True)
class Context:
    window: ReferenceWindow
    transcript: TranscriptAnnotation
    tissue: str
    model_version: str
    output_types: tuple[str, ...]
    preprocessing: str

    def validate(self) -> None:
        self.window.validate(); self.transcript.validate(self.window)
        _text(self.tissue, "tissue ontology term"); _text(self.model_version, "model version")
        require(self.tissue.startswith(("UBERON:", "CL:")), "TISSUE", "use an explicit UBERON or CL ontology identifier")
        require(bool(self.output_types) and len(set(self.output_types)) == len(self.output_types), "OUTPUT", "outputs must be unique and nonempty")
        require(set(self.output_types) <= OUTPUT_TYPES, "OUTPUT", "requested output is outside the initial adapter capabilities", "UNSUPPORTED")
        require(self.preprocessing == "forward_reference_fixed_left_v1", "PREPROCESSING", "unsupported sequence/window policy", "UNSUPPORTED")

    @property
    def settings_sha256(self) -> str:
        return identity_sha256(self)


@dataclass(frozen=True)
class Variant:
    id: str
    chromosome: str
    position: int  # one-based VCF anchor
    ref: str
    alt: str

    def validate(self) -> None:
        _text(self.id, "variant id"); _text(self.chromosome, "variant chromosome")
        _integer(self.position, "variant position")
        require(self.position > 0, "POSITION", "VCF position is one-based")
        require(isinstance(self.ref, str) and isinstance(self.alt, str) and bool(self.ref) and bool(self.alt) and set(self.ref + self.alt) <= set("ACGT"), "ALLELE", "alleles must be nonempty uppercase ACGT")
        require(self.ref != self.alt, "ALLELE", "REF and ALT must differ")


@dataclass(frozen=True)
class Phase:
    kind: str
    evidence: str

    def validate(self) -> None:
        require(isinstance(self.kind, str) and self.kind in {"cis", "trans", "unknown", "hypothetical"}, "PHASE", "unknown phase encoding")
        require(isinstance(self.evidence, str), "PHASE", "phase evidence must be text")
        if self.kind in {"cis", "trans"}:
            _text(self.evidence, "phase evidence")


@dataclass(frozen=True)
class EndpointSpec:
    id: str
    family: str
    output_type: str
    aggregation: str
    scale: str
    start0: int
    end0: int
    pseudocount: float = 0.001
    alignment: str = "reference_retained"
    site_windows: tuple[tuple[int, int], ...] = ()
    site_annotation_source: str = ""
    site_annotation_version: str = ""

    def validate(self, context: Context) -> None:
        _text(self.id, "endpoint id")
        require(self.family in FAMILIES, "ENDPOINT", "unknown endpoint family", "UNSUPPORTED")
        require(self.output_type in context.output_types, "ENDPOINT_OUTPUT", "endpoint output was not requested", "UNSUPPORTED")
        _integer(self.start0, "endpoint start"); _integer(self.end0, "endpoint end")
        require(context.window.start0 <= self.start0 < self.end0 <= context.window.end0, "ENDPOINT_WINDOW", "endpoint outside reference window")
        require(self.aggregation in {"mean", "sum", "max", "site_ratio"}, "AGGREGATION", "unsupported aggregation", "UNSUPPORTED")
        require(self.scale in {"linear", "log", "log2"}, "SCALE", "unsupported comparison scale", "UNSUPPORTED")
        require(_finite_number(self.pseudocount) and self.pseudocount > 0, "PSEUDOCOUNT", "positive pseudocount within finite floating-point range required")
        require(self.alignment == "reference_retained", "ALIGNMENT", "initial policy retains mapped reference bases, excludes insertions, zero-fills deletions", "UNSUPPORTED")
        for start, end in self.site_windows:
            require(type(start) is int and type(end) is int and self.start0 <= start < end <= self.end0, "SITE_WINDOW", "site window outside endpoint")
        if self.family == "polyadenylation" and self.site_windows:
            _text(self.site_annotation_source, "polyadenylation-site annotation source")
            _text(self.site_annotation_version, "polyadenylation-site annotation version")


@dataclass(frozen=True)
class PredictionTrack:
    output_type: str
    values: tuple[float, ...]
    interval_start0: int
    bin_size: int
    strand: str
    tissue: str
    gene_id: str
    transcript_id: str
    metadata: dict[str, Any]


@dataclass(frozen=True)
class Prediction:
    scenario: str
    sequence_sha256: str
    settings_sha256: str
    tracks: tuple[PredictionTrack, ...]
    evidence: str


@dataclass(frozen=True)
class HaplotypeRequest:
    context: Context
    variants: tuple[Variant, ...]
    phase: Phase
    endpoints: tuple[EndpointSpec, ...]

    def validate(self) -> None:
        self.context.validate(); self.phase.validate()
        require(len(self.variants) == 2, "VARIANTS", "this first interaction module requires exactly two variants", "UNSUPPORTED")
        for variant in self.variants:
            variant.validate()
        require(bool(self.endpoints) and len({e.id for e in self.endpoints}) == len(self.endpoints), "ENDPOINTS", "unique nonempty endpoint list required")
        for endpoint in self.endpoints:
            endpoint.validate(self.context)


def preflight_endpoints(context: Context, endpoints: tuple[EndpointSpec, ...]) -> None:
    """Pure semantic checks before any model call; scorer checks remain too.

    A request containing an unsupported endpoint is refused as a whole before
    prediction. The separate scoring service can still report mixed capability
    entries when analyzing already-computed predictions.
    """
    output_by_family = {"expression": "RNA_SEQ", "splice_sites": "SPLICE_SITES",
                        "splice_usage": "SPLICE_SITE_USAGE", "splice_junctions": "SPLICE_JUNCTIONS",
                        "polyadenylation": "RNA_SEQ"}
    for endpoint in endpoints:
        endpoint.validate(context)
        require(endpoint.output_type == output_by_family[endpoint.family], "FAMILY_OUTPUT", "endpoint family and model output do not match", "UNSUPPORTED")
        require(endpoint.family != "splice_junctions", "JUNCTION_ADAPTER_UNAVAILABLE", "typed splice-junction adapter is not implemented", "UNSUPPORTED")
        if endpoint.family == "expression":
            require(endpoint.aggregation in {"sum", "mean"}, "EXPRESSION_AGGREGATION", "expression requires annotated-exon sum or mean", "UNSUPPORTED")
            require(any(max(start, endpoint.start0) < min(end, endpoint.end0) for start, end in context.transcript.exons), "EMPTY_MASK", "endpoint has no annotated exon bases", "UNSUPPORTED")
        elif endpoint.family == "polyadenylation":
            require(endpoint.aggregation == "site_ratio", "FAMILY_AGGREGATION", "PAS proxy requires site_ratio aggregation", "UNSUPPORTED")
            require(len(endpoint.site_windows) == 2, "PAS_WINDOWS_REQUIRED", "declare exactly two PAS annotation windows: proximal then distal", "UNSUPPORTED")
            proximal, distal = endpoint.site_windows
            require(all(context.transcript.start0 <= start < end <= context.transcript.end0 for start, end in endpoint.site_windows), "PAS_TRANSCRIPT_WINDOW", "PAS windows must lie within the annotated transcript")
            ordered = proximal[1] <= distal[0] if context.transcript.strand == "+" else distal[1] <= proximal[0]
            require(ordered, "PAS_WINDOW_ORDER", "proximal/distal windows must be disjoint and ordered along the transcript strand")
        else:
            require(endpoint.aggregation in {"sum", "mean", "max"}, "FAMILY_AGGREGATION", "unsupported splice aggregation", "UNSUPPORTED")
            require(max(context.transcript.start0, endpoint.start0) < min(context.transcript.end0, endpoint.end0), "EMPTY_MASK", "endpoint has no annotated transcript bases", "UNSUPPORTED")


def validate_prediction(context: Context, prediction: Prediction, *, expected_sequence_sha256: str | None = None) -> None:
    require(prediction.settings_sha256 == context.settings_sha256, "MISMATCHED_SETTINGS", "prediction model/window/tissue/preprocessing differs")
    require(prediction.evidence in {"MOCK_SYNTHETIC", "REAL_MODEL_PREDICTION"}, "EVIDENCE", "prediction evidence must be explicit")
    if expected_sequence_sha256 is not None:
        require(prediction.sequence_sha256 == expected_sequence_sha256, "MISMATCHED_SEQUENCE", "prediction sequence hash differs")
    require(bool(prediction.tracks), "TRACK", "prediction has no tracks", "UNSUPPORTED")
    for track in prediction.tracks:
        require(track.output_type in context.output_types, "OUTPUT", "provider returned unrequested output")
        require(track.strand == context.transcript.strand, "STRAND", "track and transcript strands differ")
        tissue_agnostic = track.output_type == "SPLICE_SITES" and track.tissue == "TISSUE_AGNOSTIC" and track.metadata.get("tissue_specific") is False
        require(track.tissue == context.tissue or tissue_agnostic, "TISSUE", "track and requested tissue differ", "UNSUPPORTED")
        require(track.gene_id == context.transcript.gene_id and track.transcript_id == context.transcript.transcript_id, "ANNOTATION", "track annotation differs")
        require(type(track.bin_size) is int and track.bin_size > 0 and track.interval_start0 == context.window.start0, "MISMATCHED_WINDOW", "track origin/bin size differs")
        require(len(track.values) * track.bin_size == len(context.window.sequence), "MISMATCHED_WINDOW", "track does not span the matched input window")
        require(all(_finite_number(v) and v >= 0 for v in track.values), "TRACK_VALUES", "expected finite nonnegative predicted values")


def _strict_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "DUPLICATE_KEY", f"duplicate JSON field {key}")
        result[key] = value
    return result


def parse_json(text: str) -> dict:
    require(len(text.encode()) <= 8 * 2**20, "INPUT_SIZE", "request exceeds 8MiB", "RESOURCE_LIMIT")
    try:
        value = json.loads(text, object_pairs_hook=_strict_object, parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    except (ValueError, TypeError) as error:
        raise MolecularError("INVALID_INPUT", "JSON", "invalid finite JSON") from error
    require(isinstance(value, dict), "JSON", "request must be a JSON object")
    pending = [value]
    while pending:
        item = pending.pop()
        if isinstance(item, dict):
            pending.extend(item.values())
        elif isinstance(item, list):
            pending.extend(item)
        elif type(item) is float:
            require(math.isfinite(item), "JSON", "JSON floating-point number is outside finite range")
    return value


def _fields(value: dict, names: set[str], required: set[str], label: str) -> None:
    require(isinstance(value, dict) and set(value) <= names and required <= set(value), "SCHEMA", f"invalid or missing {label} fields")


def context_from_dict(value: dict) -> Context:
    names = {"window", "transcript", "tissue", "model_version", "output_types", "preprocessing"}
    _fields(value, names, names, "context")
    w, t = value["window"], value["transcript"]
    wn = set(ReferenceWindow.__dataclass_fields__); tn = set(TranscriptAnnotation.__dataclass_fields__)
    _fields(w, wn, wn, "window"); _fields(t, tn, tn, "transcript")
    try:
        require(isinstance(t["exons"], list) and all(isinstance(x, list) and len(x) == 2 for x in t["exons"]), "SCHEMA", "exons must be pairs")
        require(isinstance(value["output_types"], list) and all(isinstance(x, str) for x in value["output_types"]), "SCHEMA", "output_types must be a string array")
        context = Context(ReferenceWindow(**w), TranscriptAnnotation(**{**t, "exons": tuple(tuple(x) for x in t["exons"])}), value["tissue"], value["model_version"], tuple(value["output_types"]), value["preprocessing"])
        context.validate()
        return context
    except (TypeError, ValueError, AttributeError) as error:
        raise MolecularError("INVALID_INPUT", "SCHEMA", "malformed context") from error


def endpoint_from_dict(value: dict, context: Context) -> EndpointSpec:
    names = set(EndpointSpec.__dataclass_fields__)
    required = {"id", "family", "output_type", "aggregation", "scale", "start0", "end0"}
    _fields(value, names, required, "endpoint")
    try:
        site_windows = value.get("site_windows", [])
        require(isinstance(site_windows, list) and all(isinstance(x, list) and len(x) == 2 for x in site_windows), "SCHEMA", "site_windows must be pairs")
        endpoint = EndpointSpec(**{**value, "site_windows": tuple(tuple(x) for x in site_windows)})
        endpoint.validate(context)
        return endpoint
    except (TypeError, ValueError) as error:
        raise MolecularError("INVALID_INPUT", "SCHEMA", "malformed endpoint") from error

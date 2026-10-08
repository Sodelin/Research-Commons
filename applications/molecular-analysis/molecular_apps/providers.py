"""Thin prediction adapters. The default provider is explicitly synthetic."""
from __future__ import annotations

import importlib.util
import importlib.metadata
import os
from typing import Protocol

from .contracts import Context, MolecularError, Prediction, PredictionTrack, require, sequence_sha256


class PredictionProvider(Protocol):
    def capabilities(self, context: Context) -> dict: ...
    def predict_sequence(self, context: Context, scenario: str, sequence: str) -> Prediction: ...


class SyntheticProvider:
    """Deterministic software-test fixture, with no biological calibration."""
    OUTPUTS = {"RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE"}
    TISSUES = {"UBERON:0002107", "CL:0000540"}

    def capabilities(self, context: Context) -> dict:
        context.validate()
        require(context.model_version == "synthetic-v1", "MODEL", "mock requires explicit synthetic-v1 model", "UNSUPPORTED")
        require(context.tissue in self.TISSUES, "TISSUE", "unsupported synthetic fixture tissue", "UNSUPPORTED")
        require(set(context.output_types) <= self.OUTPUTS, "OUTPUT", "mock has no junction/ATAC capability", "UNSUPPORTED")
        return {"provider": "deterministic_mock", "evidence": "MOCK_SYNTHETIC", "model_version": "synthetic-v1", "supported_outputs": sorted(self.OUTPUTS)}

    def predict_sequence(self, context: Context, scenario: str, sequence: str) -> Prediction:
        self.capabilities(context)
        require(len(sequence) == len(context.window.sequence) and set(sequence) <= set("ACGTN"), "MISMATCHED_WINDOW", "mock sequence must match fixed window")
        weights = {"A": 1.0, "C": 2.0, "G": 3.0, "T": 4.0, "N": 0.0}
        tracks = []
        for output in context.output_types:
            if output == "RNA_SEQ":
                values = tuple(weights[b] + (2.0 if sequence[i:i+2] == "AG" else 0.0) for i, b in enumerate(sequence))
            elif output == "SPLICE_SITES":
                values = tuple(0.8 if sequence[i:i+2] in {"AG", "GT"} else 0.1 for i in range(len(sequence)))
            else:
                values = tuple(0.6 if sequence[i:i+2] in {"AG", "GT"} else 0.2 for i in range(len(sequence)))
            tracks.append(PredictionTrack(output, values, context.window.start0, 1,
                                          context.transcript.strand, context.tissue,
                                          context.transcript.gene_id, context.transcript.transcript_id,
                                          {"name": "synthetic-" + output, "synthetic": True, "coordinate_space": "edited_sequence", "fixture_rule": "deterministic-v1", "tissue_specific": True}))
        return Prediction(scenario, sequence_sha256(sequence), context.settings_sha256, tuple(tracks), "MOCK_SYNTHETIC")


class AlphaGenomeProvider:
    """Official v1 SDK wrapper; never installs software or accepts terms.

    Track names must be predeclared. Selecting the first returned experiment
    would silently change the endpoint, so this adapter refuses ambiguity.
    Junctions have a different SDK data structure and remain unsupported here.
    """
    OUTPUTS = {"RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE"}
    LENGTHS = {16384, 131072, 524288, 1048576}
    MODELS = {"ALL_FOLDS", "FOLD_0", "FOLD_1", "FOLD_2", "FOLD_3"}

    def __init__(self, *, access_authorized: bool = False, track_names: dict[str, str] | None = None):
        self.access_authorized = access_authorized
        self.track_names = track_names or {}
        self._client = None
        self._model_version = None

    def blockers(self) -> list[str]:
        blockers = []
        if importlib.util.find_spec("alphagenome") is None:
            blockers.append("official alphagenome Python SDK is not installed")
        if not self.access_authorized:
            blockers.append("authorized API access and applicable noncommercial service/output terms have not been confirmed")
        if not os.environ.get("ALPHAGENOME_API_KEY"):
            blockers.append("ALPHAGENOME_API_KEY is not configured in this process")
        return blockers

    def capabilities(self, context: Context) -> dict:
        context.validate()
        require(context.model_version in self.MODELS, "MODEL", "explicit supported official v1 model is required", "UNSUPPORTED")
        require(len(context.window.sequence) in self.LENGTHS, "WINDOW", "official model requires 16384/131072/524288/1048576 bases", "UNSUPPORTED")
        require(set(context.output_types) <= self.OUTPUTS, "OUTPUT", "junction adapter and other output modalities are not yet implemented", "UNSUPPORTED")
        require(set(context.output_types) <= set(self.track_names), "TRACK_SELECTION", "predeclare one exact track name per requested modality", "UNSUPPORTED")
        blockers = self.blockers()
        if blockers:
            raise MolecularError("UNSUPPORTED", "LIVE_ACCESS_PENDING", "; ".join(blockers))
        return {"provider": "official_alphagenome_v1_sdk", "model_version": context.model_version,
                "evidence": "REAL_MODEL_PREDICTION", "tissue_output_support": "requires metadata validation before inference", "quota": "not preverified"}

    def _get_client(self, context: Context):
        self.capabilities(context)
        from alphagenome.models.v1 import dna_client, dna_model
        if self._client is None:
            self._client = dna_client.create(os.environ["ALPHAGENOME_API_KEY"], model_version=dna_model.ModelVersion[context.model_version], timeout=30)
            self._model_version = context.model_version
        require(self._model_version == context.model_version, "MODEL", "a provider instance cannot switch model versions")
        return self._client

    def predict_sequence(self, context: Context, scenario: str, sequence: str) -> Prediction:
        require(len(sequence) == len(context.window.sequence) and set(sequence) <= set("ACGTN"), "MISMATCHED_WINDOW", "sequence and fixed context window differ")
        try:
            client = self._get_client(context)
            from alphagenome.data import genome
            from alphagenome.models.v1 import dna_model, dna_output
            metadata = client.output_metadata(dna_model.Organism.HOMO_SAPIENS)
            for output in context.output_types:
                frame = metadata.get(dna_output.OutputType[output])
                self._select_row(frame, output, context)
            interval = genome.Interval(context.window.chromosome, context.window.start0, context.window.end0, strand="+")
            outputs = client.predict_sequence(sequence, organism=dna_model.Organism.HOMO_SAPIENS,
                                              requested_outputs=[dna_output.OutputType[x] for x in context.output_types],
                                              ontology_terms=[context.tissue], interval=interval)
            tracks = []
            for output in context.output_types:
                raw = outputs.get(dna_output.OutputType[output])
                require(raw is not None, "OUTPUT", "model omitted requested output", "UNSUPPORTED")
                index, row = self._select_row(raw.metadata, output, context)
                require(raw.values.ndim == 2, "OUTPUT_SHAPE", "adapter requires positional track data", "UNSUPPORTED")
                require(raw.interval is not None and raw.interval.start == context.window.start0 and raw.interval.end == context.window.end0, "MISMATCHED_WINDOW", "SDK output interval differs")
                tissue = "TISSUE_AGNOSTIC" if output == "SPLICE_SITES" and "ontology_curie" not in row else str(row.get("ontology_curie"))
                tracks.append(PredictionTrack(output, tuple(float(v) for v in raw.values[:, index]), raw.interval.start, raw.resolution,
                                              str(row["strand"]), tissue, context.transcript.gene_id, context.transcript.transcript_id,
                                              {"name": str(row["name"]), "synthetic": False, "coordinate_space": "edited_sequence",
                                               "tissue_specific": tissue != "TISSUE_AGNOSTIC", "annotation_ids": "supplied annotation, not inferred by model",
                                               "sdk_adapter": "official-v1", "sdk_version": importlib.metadata.version("alphagenome"),
                                               "model_version": context.model_version, "immutable_server_weights": "not exposed by API"}))
            return Prediction(scenario, sequence_sha256(sequence), context.settings_sha256, tuple(tracks), "REAL_MODEL_PREDICTION")
        except MolecularError:
            raise
        except Exception as error:
            # Never propagate raw SDK exception text: it can carry request metadata.
            code = getattr(error, "code", None)
            name = str(code()) if callable(code) else type(error).__name__
            status = "RESOURCE_LIMIT" if "RESOURCE_EXHAUSTED" in name or "DEADLINE_EXCEEDED" in name else "EXECUTION_FAILURE"
            raise MolecularError(status, "SDK_REQUEST", "official SDK request failed (" + name + "); no biological result established") from error

    def _select_row(self, frame, output: str, context: Context):
        require(frame is not None, "OUTPUT", "selected output has no model metadata", "UNSUPPORTED")
        selected = []
        for index, (_, row) in enumerate(frame.iterrows()):
            row = row.to_dict()
            tissue_match = row.get("ontology_curie") == context.tissue or (output == "SPLICE_SITES" and "ontology_curie" not in row)
            if row.get("name") == self.track_names[output] and row.get("strand") == context.transcript.strand and tissue_match:
                selected.append((index, row))
        require(len(selected) == 1, "TISSUE_OUTPUT", "exact track/strand/tissue selection is unavailable or ambiguous", "UNSUPPORTED")
        return selected[0]

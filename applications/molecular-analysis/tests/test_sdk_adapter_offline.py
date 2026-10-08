"""Synthetic SDK-interface doubles. These tests never load or call the SDK."""
from dataclasses import replace
import sys
import types
import unittest
from unittest import mock

from molecular_apps.contracts import MolecularError, context_from_dict, sequence_sha256, validate_prediction
from molecular_apps.providers import AlphaGenomeProvider
from tests.test_contracts_and_cli import fixture


class Row:
    def __init__(self, data): self.data = data
    def to_dict(self): return dict(self.data)


class Frame:
    def __init__(self, rows): self.rows = rows
    def iterrows(self): return ((i, Row(r)) for i, r in enumerate(self.rows))


class Values:
    ndim = 2
    def __init__(self, length): self.length = length
    def __getitem__(self, key):
        positions, column = key
        assert positions == slice(None) and column == 0
        return [0.25] * self.length


def interval(chromosome, start, end, strand="+"):
    return types.SimpleNamespace(chromosome=chromosome, start=start, end=end, strand=strand)


class MappingOutputs:
    def __init__(self, outputs): self.outputs = outputs
    def get(self, kind): return self.outputs.get(kind)


class Client:
    def __init__(self, context, rows=None, failure=None):
        self.context = context; self.calls = []; self.failure = failure
        self.rows = rows or [{"name": "predeclared-RNA", "strand": "+", "ontology_curie": context.tissue}]
    def output_metadata(self, organism):
        return MappingOutputs({"RNA_SEQ": Frame(self.rows)})
    def predict_sequence(self, sequence, **kwargs):
        self.calls.append((sequence, kwargs))
        if self.failure: raise self.failure
        raw = types.SimpleNamespace(values=Values(len(sequence)), metadata=Frame(self.rows),
                                    resolution=1, interval=kwargs["interval"])
        return MappingOutputs({"RNA_SEQ": raw})


def sdk_doubles():
    module = types.ModuleType("alphagenome.data")
    module.genome = types.SimpleNamespace(Interval=interval)
    v1 = types.ModuleType("alphagenome.models.v1")
    v1.dna_model = types.SimpleNamespace(Organism=types.SimpleNamespace(HOMO_SAPIENS="synthetic-human-enum"))
    v1.dna_output = types.SimpleNamespace(OutputType={"RNA_SEQ": "RNA_SEQ"})
    return {"alphagenome": types.ModuleType("alphagenome"), "alphagenome.data": module,
            "alphagenome.models": types.ModuleType("alphagenome.models"), "alphagenome.models.v1": v1}


class SDKInterfaceDoubleTests(unittest.TestCase):
    def context(self):
        c = context_from_dict(fixture()["context"])
        sequence = "ACGT" * 4096
        w = replace(c.window, sequence=sequence, sha256=sequence_sha256(sequence + c.window.guard_sequence))
        return replace(c, window=w, model_version="ALL_FOLDS", output_types=("RNA_SEQ",))

    def predict_with_double(self, client):
        c = client.context
        provider = AlphaGenomeProvider(track_names={"RNA_SEQ": "predeclared-RNA"})
        with mock.patch.dict(sys.modules, sdk_doubles()), mock.patch.object(provider, "_get_client", return_value=client), mock.patch("molecular_apps.providers.importlib.metadata.version", return_value="SYNTHETIC_INTERFACE_DOUBLE"):
            return provider.predict_sequence(c, "REF", c.window.sequence)

    def test_sdk_signature_and_exact_selection(self):
        c = self.context(); client = Client(c); p = self.predict_with_double(client)
        validate_prediction(c, p, expected_sequence_sha256=sequence_sha256(c.window.sequence))
        self.assertEqual(client.calls[0][0], c.window.sequence)
        settings = client.calls[0][1]
        self.assertEqual(settings["ontology_terms"], [c.tissue])
        self.assertEqual(settings["requested_outputs"], ["RNA_SEQ"])
        self.assertEqual(settings["interval"].start, c.window.start0)
        self.assertEqual(settings["interval"].end, c.window.end0)
        self.assertEqual(p.tracks[0].metadata["sdk_version"], "SYNTHETIC_INTERFACE_DOUBLE")
        # REAL_MODEL_PREDICTION is the adapter's production label; this injected
        # double is only a unit test. No returned object is published as live evidence.

    def test_missing_tissue_refused_before_inference(self):
        c = self.context(); client = Client(c, rows=[{"name": "predeclared-RNA", "strand": "+", "ontology_curie": "CL:9999"}])
        with self.assertRaises(MolecularError) as error: self.predict_with_double(client)
        self.assertEqual(error.exception.status, "UNSUPPORTED"); self.assertEqual(client.calls, [])

    def test_wrong_strand_refused_before_inference(self):
        c = self.context(); client = Client(c, rows=[{"name": "predeclared-RNA", "strand": "-", "ontology_curie": c.tissue}])
        with self.assertRaises(MolecularError): self.predict_with_double(client)
        self.assertEqual(client.calls, [])

    def test_ambiguous_track_refused_before_inference(self):
        c = self.context(); row = {"name": "predeclared-RNA", "strand": "+", "ontology_curie": c.tissue}
        client = Client(c, rows=[row, row])
        with self.assertRaises(MolecularError): self.predict_with_double(client)
        self.assertEqual(client.calls, [])

    def test_quota_failure_is_resource_limit(self):
        class QuotaError(Exception):
            def code(self): return "StatusCode.RESOURCE_EXHAUSTED"
        client = Client(self.context(), failure=QuotaError("synthetic quota failure"))
        with self.assertRaises(MolecularError) as error: self.predict_with_double(client)
        self.assertEqual(error.exception.status, "RESOURCE_LIMIT")

    def test_execution_failure_is_separate(self):
        client = Client(self.context(), failure=RuntimeError("synthetic failure"))
        with self.assertRaises(MolecularError) as error: self.predict_with_double(client)
        self.assertEqual(error.exception.status, "EXECUTION_FAILURE")


if __name__ == "__main__":
    unittest.main()

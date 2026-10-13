"""Malformed-evidence controls for the intake helper, not Rust/Lean tests."""
import base64
import gzip
import importlib.util
import json
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("intake", Path(__file__).with_name("audit_intake.py"))
intake = importlib.util.module_from_spec(spec)
spec.loader.exec_module(intake)


class IntakeControls(unittest.TestCase):
    def envelope(self, raw):
        packed = gzip.compress(raw, mtime=0)
        return dict(payload=base64.b64encode(packed).decode(), gzip_bytes=len(packed),
                    gzip_sha256=intake.sha(packed), expanded_bytes=len(raw), expanded_sha256=intake.sha(raw))

    def test_valid_exact_envelope(self):
        self.assertEqual(intake.unbundle(self.envelope(b'{"x": 1}')), {"x": 1})

    def test_equal_length_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, "SHA256"):
            intake.identity(b"bad", dict(bytes=3, sha256=intake.sha(b"yes")))

    def test_truncated_content_rejected(self):
        with self.assertRaisesRegex(ValueError, "byte count"):
            intake.identity(b"ye", dict(bytes=3, sha256=intake.sha(b"yes")))

    def test_changed_expansion_identity_rejected(self):
        row = self.envelope(b'{"x": 1}')
        row["expanded_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SHA256"):
            intake.unbundle(row)

    def test_oversized_expansion_refused_before_decode(self):
        with self.assertRaisesRegex(ValueError, "exceeds cap"):
            intake.unbundle(dict(expanded_bytes=intake.MAX_PACKET + 1, payload="invalid"))

    def test_invalid_base64_rejected(self):
        row = self.envelope(b"{}")
        row["payload"] += "!"
        with self.assertRaises(ValueError):
            intake.unbundle(row)

    def test_unknown_encoding_refused(self):
        with self.assertRaisesRegex(ValueError, "unsupported"):
            intake.embedded_bytes(dict(encoding="approximate", content="{}"))


if __name__ == "__main__":
    unittest.main(verbosity=2)

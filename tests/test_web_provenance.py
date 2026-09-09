import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1] / "solver" / "tools"
sys.path.insert(0, str(TOOLS))
import provenance
from verify_web_build import local_path_marker_count, verify_manifest


class WebProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.output = Path(self.tmp.name)
        for name in provenance.WEB_ARTIFACTS:
            (self.output / name).write_bytes(name.encode())
        self.manifest = {
            "schemaVersion": 1, "crate": "navier-web",
            "compiledSources": list(provenance.COMPILED_SOURCES),
            "sourceDigest": provenance.source_digest(),
            "buildInputs": list(provenance.BUILD_INPUTS),
            "buildPipelineDigest": provenance.build_pipeline_digest(),
            "cargoLockSha256": provenance.sha256(provenance.CRATE_DIR / "Cargo.lock"),
            "continuumCertificate": False, "adaptiveRecording": False,
            "reproducibility": {
                "rustPathRemapping": True,
                "localAbsolutePathGuard": True,
            },
            "artifacts": {name: provenance.sha256(self.output / name) for name in provenance.WEB_ARTIFACTS},
        }

    def test_complete_build_and_tampered_wasm(self):
        self.assertEqual(verify_manifest(self.output, self.manifest), [])
        (self.output / "navier_web_bg.wasm").write_bytes(b"tampered")
        self.assertTrue(any("artifact hash mismatch" in error for error in verify_manifest(self.output, self.manifest)))

    def test_empty_or_outside_artifact_inventory_cannot_pass(self):
        for artifacts in [{}, {"../outside.wasm": "sha256-anything"}]:
            with self.subTest(artifacts=artifacts):
                self.manifest["artifacts"] = artifacts
                self.assertTrue(verify_manifest(self.output, self.manifest))

    def test_local_absolute_path_marker_cannot_pass_or_leak_path(self):
        wasm = self.output / "navier_web_bg.wasm"
        wasm.write_bytes(b"prefix:/Users/example/private/source.rs:suffix")
        self.manifest["artifacts"][wasm.name] = provenance.sha256(wasm)
        failures = verify_manifest(self.output, self.manifest)
        self.assertEqual(local_path_marker_count(wasm.read_bytes()), 1)
        self.assertTrue(any("local absolute path marker" in error for error in failures))
        self.assertNotIn("example", " ".join(failures))

    def test_missing_reproducibility_policy_cannot_pass(self):
        self.manifest.pop("reproducibility")
        self.assertTrue(verify_manifest(self.output, self.manifest))

    def test_incomplete_sources_and_false_certification_cannot_pass(self):
        self.manifest["compiledSources"] = []
        self.assertTrue(verify_manifest(self.output, self.manifest))
        self.manifest["compiledSources"] = list(provenance.COMPILED_SOURCES)
        self.manifest["continuumCertificate"] = True
        self.assertTrue(verify_manifest(self.output, self.manifest))

    def test_future_shader_is_automatically_included_and_bound(self):
        crate = self.output / "crate"
        shader = crate / "src" / "nested" / "future.wgsl"
        shader.parent.mkdir(parents=True)
        shader.write_text("first")
        for name in ["Cargo.toml", "Cargo.lock"]:
            (crate / name).write_text(name)
        with patch.object(provenance, "CRATE_DIR", crate):
            sources = provenance.compiled_sources()
            self.assertIn("src/nested/future.wgsl", sources)
            with patch.object(provenance, "COMPILED_SOURCES", sources):
                before = provenance.source_digest()
                shader.write_text("second")
                self.assertNotEqual(before, provenance.source_digest())


if __name__ == "__main__":
    unittest.main()

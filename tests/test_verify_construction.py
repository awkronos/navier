import importlib.util
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "verify_construction.py"
SPEC = importlib.util.spec_from_file_location("verify_construction", SCRIPT)
verify = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(verify)


class VerifyConstructionTests(unittest.TestCase):
    def write_project(self, root: Path) -> None:
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
        (root / "lakefile.toml").write_text('name = "Fixture"\n')
        for module, source in {
            "Fixture.Root": "/- import Ignored.Fake -/\nimport Fixture.Left Fixture.Leaf\n",
            "Fixture.Left": "-- import Ignored.Line\nimport Fixture.Leaf\n",
            "Fixture.Leaf": "def leaf := 1\n",
        }.items():
            path = verify.module_path(root, module)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)

    def test_local_closure_is_dependency_ordered_and_ignores_comments(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_project(root)
            graph = verify.local_import_graph(root, "Fixture.Root")
            self.assertEqual(graph["Fixture.Root"], ["Fixture.Left", "Fixture.Leaf"])
            self.assertEqual(
                verify.dependency_order(graph, "Fixture.Root"),
                ["Fixture.Leaf", "Fixture.Left", "Fixture.Root"],
            )

    def test_leaf_change_invalidates_every_transitive_dependent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_project(root)
            graph = verify.local_import_graph(root, "Fixture.Root")
            order = verify.dependency_order(graph, "Fixture.Root")
            environment = verify.environment_fingerprint(root)
            before = verify.compute_fingerprints(root, graph, order, environment)
            receipts = {module: {
                "fingerprint": before[module]["fingerprint"],
                "exit_code": 0,
                "output_sha256": verify.sha256(b""),
            } for module in order}
            olean_root = root / ".lake" / "build" / "lib" / "lean"
            for module in order:
                output = olean_root / (module.replace(".", "/") + ".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                output.touch()
            self.assertEqual(verify.fresh_modules(order, graph, before, receipts, olean_root), set(order))

            leaf_output = olean_root / "Fixture" / "Leaf.olean"
            leaf_output.unlink()
            self.assertEqual(verify.fresh_modules(order, graph, before, receipts, olean_root), set())
            leaf_output.touch()

            verify.module_path(root, "Fixture.Leaf").write_text("def leaf := 2\n")
            after = verify.compute_fingerprints(root, graph, order, environment)
            self.assertEqual(verify.fresh_modules(order, graph, after, receipts, olean_root), set())

    def test_axiom_parser_exposes_nonstandard_dependencies(self):
        standard = (
            "'Example.result' depends on axioms: [propext,\n"
            " Classical.choice,\n Quot.sound]\n"
        )
        self.assertEqual(verify.parse_axioms(standard, "Example.result"), verify.ALLOWED_AXIOMS)
        unsafe = "'Example.result' depends on axioms: [propext, sorryAx]\n"
        self.assertIn("sorryAx", verify.parse_axioms(unsafe, "Example.result") - verify.ALLOWED_AXIOMS)

    def test_receipts_require_matching_fingerprint_and_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "A.olean"
            fingerprint = {"A": {"fingerprint": "current"}}
            receipts = {"A": {"fingerprint": "stale"}}
            output.touch()
            graph = {"A": []}
            self.assertEqual(verify.fresh_modules(["A"], graph, fingerprint, receipts, root), set())
            receipts["A"]["fingerprint"] = "current"
            # A legacy receipt without checked output bytes is not fresh.
            self.assertEqual(verify.fresh_modules(["A"], graph, fingerprint, receipts, root), set())
            receipts["A"].update(exit_code=0, output_sha256=verify.sha256(b""))
            self.assertEqual(verify.fresh_modules(["A"], graph, fingerprint, receipts, root), {"A"})
            output.write_bytes(b"different compiled object")
            self.assertEqual(verify.fresh_modules(["A"], graph, fingerprint, receipts, root), set())

    def test_changed_compiled_dependency_invalidates_consumers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph = {"A": [], "B": ["A"]}
            fingerprints = {name: {"fingerprint": name} for name in graph}
            receipts = {}
            for name in graph:
                (root / f"{name}.olean").write_bytes(name.encode())
                receipts[name] = {"fingerprint": name, "exit_code": 0,
                                  "output_sha256": verify.sha256(name.encode())}
            self.assertEqual(verify.fresh_modules(graph, graph, fingerprints, receipts, root), {"A", "B"})
            (root / "A.olean").write_bytes(b"replacement")
            self.assertEqual(verify.fresh_modules(graph, graph, fingerprints, receipts, root), set())


if __name__ == "__main__":
    unittest.main()

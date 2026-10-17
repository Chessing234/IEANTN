"""Regression coverage for the assembled Palomar module layout."""
import json
import unittest.mock
from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestSpinoffLayout(FixtureRepo):
    def emit(self, global_name=False):
        self.write_node("A.v1", LITERATURE)
        nodes = ieantn.load_nodes()
        nodes["A.v1"]["conclusions"][0]["justifications"][0]["kind"] = "lean-comparator"
        solution = self.root / "Solutions" / "A.v1"
        solution.mkdir(parents=True)
        (solution / "Solution.lean").write_text("import Helper\ntheorem A.v1.challenge_main : A.v1.main := trivial\n")
        (solution / "Helper.lean").write_text("import IEANTN.Nodes.A.v1.Conclusions\n")
        source = self.root / "IEANTN" / "Nodes" / "A" / "v1" / "Conclusions.lean"
        name = "A.v1.main" if global_name else "main"
        source.write_text(f"import Mathlib\ndef {name} : Prop := True\n")
        decl = dict(module="IEANTN.Nodes.A.v1.Conclusions", name="A.v1.main",
                    startLine=2, startCol=0, endLine=2, endCol=len(f"def {name} : Prop := True"),
                    nameStartLine=2, nameStartCol=4, nameEndLine=2, nameEndCol=4 + len(name))
        result = ieantn.subprocess.CompletedProcess([], 0, json.dumps({"declarations": [decl]}), "")
        with unittest.mock.patch.object(ieantn, "load_nodes", return_value=nodes), \
             unittest.mock.patch.object(ieantn.subprocess, "run", return_value=result):
            self.assertTrue(ieantn.spinoff("A.v1.main", "export", False))
        return self.root / "export"

    def test_wrapper_imports_vendored_proof_without_importing_itself(self):
        target = self.emit()
        imports = ieantn.imports_of(target / "Solution.lean")
        self.assertEqual(imports, ["Helper", "NodeSolution"])
        self.assertIn("theorem A.v1.challenge_main", (target / "NodeSolution.lean").read_text())
        self.assertIn("namespace A.v1\n", (target / "Challenge.lean").read_text())
        self.assertIn("end A.v1\n", (target / "Challenge.lean").read_text())

    def test_fully_qualified_definition_does_not_emit_unmatched_end(self):
        target = self.emit(global_name=True)
        challenge = (target / "Challenge.lean").read_text()
        self.assertNotIn("\nend ", challenge)
        self.assertIn("def A.v1.main : Prop := True", challenge)

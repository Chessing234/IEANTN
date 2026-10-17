"""`lean-noncompliant`: the proof is here, and Comparator cannot be run on it."""
import contextlib
import io
import unittest.mock

from test_ieantn import FixtureRepo, LITERATURE, bridged, ieantn

NONCOMPLIANT = """
- id: main
  declaration: {node}.main
  challenge: {node}.challenge_main
  imports: []
  imports_status: none
  issue: 7
  justifications:
    - id: port
      kind: lean-noncompliant
      note: >-
        The finite certificates come from a LeanCert pin nobody has admitted yet.
  designated: port
"""


class TestNoncompliantLean(FixtureRepo):
    def write_solution(self, node_id: str = "A.v1") -> None:
        directory = self.root / "Solutions" / node_id
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "Solution.lean").write_text("-- the proof\n", encoding="utf-8")

    def test_a_supplied_proof_with_its_obstruction_named_is_accepted(self) -> None:
        self.write_node("A.v1", NONCOMPLIANT)
        self.write_solution()
        self.assertTrue(ieantn.check_graph())
        conclusion = ieantn.conclusions_of(ieantn.load_nodes()["A.v1"])[0]
        self.assertEqual(ieantn.designated_kind(conclusion), "lean-noncompliant")

    def test_it_is_not_verified_and_gets_no_receipt(self) -> None:
        """The kind exists precisely to say that nothing in this network checked the proof."""
        self.write_node("A.v1", NONCOMPLIANT)
        self.write_solution()
        self.assertNotIn("lean-noncompliant", ieantn.VERIFIED_KINDS)
        conclusion = ieantn.conclusions_of(ieantn.load_nodes()["A.v1"])[0]
        # No receipt is consulted, so no receipt can be found missing.
        self.assertIsNone(ieantn.receipt_state("A.v1.main", conclusion))
        self.assertEqual(ieantn.display_kind("A.v1.main", conclusion), "lean-noncompliant")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed),              unittest.mock.patch.object(ieantn, "compute_fingerprints", return_value={}):
            ieantn.status()
        self.assertIn("has not certified", printed.getvalue())

    def test_the_proof_must_actually_be_there(self) -> None:
        """Otherwise the kind is `asserted` wearing a borrowed coat."""
        self.write_node("A.v1", NONCOMPLIANT)
        self.assertFalse(ieantn.check_graph())

    def test_the_obstruction_must_be_named(self) -> None:
        """Nobody can tell whether an unrecorded obstruction is still there."""
        self.write_node("A.v1", NONCOMPLIANT.replace(
            "      note: >-\n"
            "        The finite certificates come from a LeanCert pin nobody has admitted yet.\n",
            ""))
        self.write_solution()
        self.assertFalse(ieantn.check_graph())

    def test_the_tracking_issue_is_asked_for_but_not_required(self) -> None:
        self.write_node("A.v1", NONCOMPLIANT.replace("  issue: 7\n", ""))
        self.write_solution()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertTrue(ieantn.check_graph())
        self.assertIn("names no `issue`", printed.getvalue())

    def test_housekeeping_queues_it_as_work_on_the_obstruction(self) -> None:
        """Not `justify` -- the proof exists. What is outstanding is the certificate."""
        self.write_node("A.v1", NONCOMPLIANT)
        self.write_solution()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.housekeeping()
        output = printed.getvalue()
        self.assertIn("certify   A.v1.main", output)
        self.assertNotIn("justify   A.v1.main", output)

    def test_it_outranks_a_citation_and_is_outranked_by_a_bridge(self) -> None:
        self.write_node("A.v1", NONCOMPLIANT)
        self.write_solution()
        self.write_node("B.v1", LITERATURE)
        self.write_node("C.v1", bridged("A.v1.main"))
        nodes = ieantn.load_nodes()
        order = ieantn.EVIDENCE_ORDER
        self.assertGreater(
            order.index(ieantn.weakest_kind("A.v1", ieantn.conclusions_of(nodes["A.v1"]))),
            order.index(ieantn.weakest_kind("B.v1", ieantn.conclusions_of(nodes["B.v1"]))),
        )
        self.assertLess(
            order.index(ieantn.weakest_kind("A.v1", ieantn.conclusions_of(nodes["A.v1"]))),
            order.index(ieantn.weakest_kind("C.v1", ieantn.conclusions_of(nodes["C.v1"]))),
        )

    def test_it_is_drawn_in_the_graph_and_counted_in_the_state_snapshot(self) -> None:
        self.write_node("A.v1", NONCOMPLIANT)
        self.write_solution()
        nodes = ieantn.load_nodes()
        self.assertIn("| `lean-noncompliant` | 1 |", ieantn.render_state(nodes))
        self.assertIn("weakest: lean, noncompliant", ieantn.render_graph(nodes))

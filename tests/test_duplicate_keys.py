"""A key written twice: the one metadata error that reads as success."""
import pathlib

from test_ieantn import FixtureRepo, LITERATURE, ieantn


def repeat(path: pathlib.Path, line: str, again: str) -> None:
    """Write `again` directly after `line`, at that line's own indentation."""
    out = []
    for existing in path.read_text(encoding="utf-8").splitlines(keepends=True):
        out.append(existing)
        if existing.strip() == line:
            indent = existing[: len(existing) - len(existing.lstrip())]
            out.append(f"{indent}{again}\n")
    path.write_text("".join(out), encoding="utf-8")


class TestDuplicateKeys(FixtureRepo):
    def test_a_repeated_key_in_a_conclusion_is_reported_with_its_line(self) -> None:
        """The FKS.v1 case: `imports_status` twice, PyYAML keeping the one written last."""
        directory = self.write_node("A.v1", LITERATURE.replace(
            "  imports: []\n", "  imports: []\n  imports_status: traced\n"))
        path = directory / "formalization.yaml"
        repeat(path, "designated: paper", "imports_status: none")

        # Nothing else objects: the file parses, and what it parses to is well-formed.
        self.assertEqual(ieantn.import_status(
            ieantn.conclusions_of(ieantn.load_nodes()["A.v1"])[0]), "none")
        self.assertFalse(ieantn.check_graph())

        duplicates = ieantn.duplicate_keys(path.read_text(encoding="utf-8"))
        self.assertEqual(len(duplicates), 1)
        container, key, line = duplicates[0]
        self.assertEqual((container, key), ("conclusions[0]", "imports_status"))
        # The line reported is the second occurrence -- the one PyYAML keeps.
        numbered = path.read_text(encoding="utf-8").splitlines()
        self.assertEqual(numbered[line - 1].strip(), "imports_status: none")

    def test_the_same_key_in_two_sibling_mappings_is_not_a_duplicate(self) -> None:
        """Otherwise every node with two conclusions would be reported."""
        self.write_node("A.v1", LITERATURE + LITERATURE.replace("main", "other"))
        self.assertTrue(ieantn.check_graph())

    def test_a_repeat_in_the_node_block_is_reported_against_that_block(self) -> None:
        directory = self.write_node("A.v1", LITERATURE)
        path = directory / "formalization.yaml"
        repeat(path, "status: active", "status: deprecated")
        self.assertFalse(ieantn.check_graph())
        self.assertEqual([(container, key) for container, key, _ in
                          ieantn.duplicate_keys(path.read_text(encoding="utf-8"))],
                         [("node", "status")])

    def test_an_inactive_node_is_checked_too(self) -> None:
        """A duplicate there is what would stop `reactivate` writing the file back."""
        directory = self.write_node("A.v1", LITERATURE, status="inactive")
        path = directory / "formalization.yaml"
        repeat(path, "family: A", "inactive_reason: Unused.")
        repeat(path, "version: v1", "family: A")
        self.assertFalse(ieantn.check_graph())

    def test_a_clean_file_reports_nothing(self) -> None:
        directory = self.write_node("A.v1", LITERATURE)
        self.assertEqual(
            ieantn.duplicate_keys(
                (directory / "formalization.yaml").read_text(encoding="utf-8")), [])
        self.assertTrue(ieantn.check_graph())

    def test_it_looks_inside_nested_sequences(self) -> None:
        """Justifications are a list of mappings, which is where a repeat is least visible."""
        found = ieantn.duplicate_keys(
            "conclusions:\n"
            "- id: main\n"
            "  justifications:\n"
            "  - id: paper\n"
            "    kind: literature\n"
            "    kind: asserted\n")
        self.assertEqual(found, [("conclusions[0].justifications[0]", "kind", 6)])

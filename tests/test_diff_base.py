"""A failed Git read is not an empty network baseline."""
import contextlib
import io
import subprocess
from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestDiffBase(FixtureRepo):
    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True,
                              capture_output=True, text=True)

    def setUp(self):
        super().setUp()
        self.git("init", "-q")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-m", "Empty base")

    def test_unknown_base_does_not_report_all_conclusions_as_new(self):
        self.write_node("A.v1", LITERATURE)
        output = io.StringIO()
        with contextlib.redirect_stdout(output), self.assertRaisesRegex(SystemExit, "cannot read network base"):
            ieantn.diff("missing-base")
        self.assertNotIn("new conclusion", output.getvalue())

    def test_valid_empty_base_is_still_supported(self):
        self.write_node("A.v1", LITERATURE)
        self.assertTrue(ieantn.diff("HEAD"))
        self.assertEqual(ieantn.state_at("HEAD")["conclusions"], {})

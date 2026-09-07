import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
VALID_MANIFEST = """\
version: 1
generated_from: README.md
nodes:
  - id: sample
    type: theorem
    status: verified
    summary: Minimal valid node
    dependencies: []
    owner: mainline
    worktree: codex/test
    source_paths:
      - README.md
    acceptance_command: test -f README.md
    evidence:
      - README.md
"""


class DagStatusTests(unittest.TestCase):
    def run_manifest(self, contents: str) -> subprocess.CompletedProcess[str]:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".yaml", dir=REPO_ROOT, delete=False
        ) as manifest:
            manifest.write(contents)
            manifest_path = Path(manifest.name)
        try:
            return subprocess.run(
                ["scripts/dag_status.sh", str(manifest_path)],
                cwd=REPO_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            manifest_path.unlink()

    def test_accepts_valid_manifest(self) -> None:
        result = self.run_manifest(VALID_MANIFEST)

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("validation=ok", result.stdout)

    def test_rejects_missing_source_path(self) -> None:
        manifest = VALID_MANIFEST.replace("README.md\n    acceptance_command", "THIS_PATH_DOES_NOT_EXIST.lean\n    acceptance_command", 1)

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("references missing source path: THIS_PATH_DOES_NOT_EXIST.lean", result.stdout)

    def test_rejects_missing_acceptance_command(self) -> None:
        manifest = VALID_MANIFEST.replace(
            "    acceptance_command: test -f README.md\n", ""
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("node sample is missing required field: acceptance_command", result.stdout)

    def test_rejects_malformed_yaml(self) -> None:
        manifest = VALID_MANIFEST.replace(
            "summary: Minimal valid node", "summary: [unterminated"
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid YAML", result.stdout)

    def test_requires_every_documented_node_field(self) -> None:
        fields = {
            "type": "    type: theorem\n",
            "status": "    status: verified\n",
            "summary": "    summary: Minimal valid node\n",
            "dependencies": "    dependencies: []\n",
            "owner": "    owner: mainline\n",
            "worktree": "    worktree: codex/test\n",
            "source_paths": "    source_paths:\n      - README.md\n",
            "acceptance_command": "    acceptance_command: test -f README.md\n",
            "evidence": "    evidence:\n      - README.md\n",
        }
        for field, declaration in fields.items():
            with self.subTest(field=field):
                result = self.run_manifest(VALID_MANIFEST.replace(declaration, ""))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(
                    f"node sample is missing required field: {field}", result.stdout
                )

        result = self.run_manifest(VALID_MANIFEST.replace("  - id: sample\n", "  -\n", 1))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("node entry 1 is missing required field: id", result.stdout)


if __name__ == "__main__":
    unittest.main()

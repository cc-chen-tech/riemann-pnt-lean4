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
    proof_category: lean_theorem
    closure_state: closed
    status: verified
    summary: Minimal valid node
    dependencies: []
    owner: mainline
    worktree: codex/test
    source_paths:
      - README.md
    acceptance_command: test -f README.md
    evidence:
      - path: README.md
        commit: "0000000000000000000000000000000000000000"
        command: test -f README.md
        exit_code: 0
        proof_category: lean_theorem
        claim_scope: Minimal test fixture only
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
            "proof_category": "    proof_category: lean_theorem\n",
            "closure_state": "    closure_state: closed\n",
            "status": "    status: verified\n",
            "summary": "    summary: Minimal valid node\n",
            "dependencies": "    dependencies: []\n",
            "owner": "    owner: mainline\n",
            "worktree": "    worktree: codex/test\n",
            "source_paths": "    source_paths:\n      - README.md\n",
            "acceptance_command": "    acceptance_command: test -f README.md\n",
            "evidence": "    evidence:\n      - path: README.md\n        commit: \"0000000000000000000000000000000000000000\"\n        command: test -f README.md\n        exit_code: 0\n        proof_category: lean_theorem\n        claim_scope: Minimal test fixture only\n",
        }
        for field, declaration in fields.items():
            with self.subTest(field=field):
                result = self.run_manifest(VALID_MANIFEST.replace(declaration, "", 1))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(
                    f"node sample is missing required field: {field}", result.stdout
                )

        result = self.run_manifest(VALID_MANIFEST.replace("  - id: sample\n", "  -\n", 1))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("node entry 1 is missing required field: id", result.stdout)

    def test_rejects_dag_self_check_as_theorem_closure(self) -> None:
        manifest = VALID_MANIFEST.replace(
            "test -f README.md", "scripts/dag_status.sh proof-dag.yaml"
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot use structure", result.stdout)

    def test_rejects_axiom_audit_as_theorem_closure(self) -> None:
        manifest = VALID_MANIFEST.replace(
            "test -f README.md", "lake env lean Test/ExampleAxiomAudit.lean"
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot use structure", result.stdout)

    def test_rejects_conditional_interface_as_closed_theorem(self) -> None:
        manifest = VALID_MANIFEST.replace(
            "proof_category: lean_theorem", "proof_category: conditional_interface"
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot close proof_category conditional_interface", result.stdout)

    def test_rejects_untraceable_verified_evidence(self) -> None:
        manifest = VALID_MANIFEST.replace(
            'commit: "0000000000000000000000000000000000000000"',
            'commit: "short-sha"',
        )

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must name a full commit SHA", result.stdout)

    def test_rejects_missing_verified_evidence_path(self) -> None:
        manifest = VALID_MANIFEST.replace("path: README.md", "path: missing-evidence.log")

        result = self.run_manifest(manifest)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("references missing path", result.stdout)


if __name__ == "__main__":
    unittest.main()

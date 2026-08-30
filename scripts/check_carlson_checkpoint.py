#!/usr/bin/env python3
"""Build the frozen Carlson checkpoint and audit every requested axiom report.

This is a branch-scoped check, not a replacement for verify-baseline.sh.
Logs and machine-readable evidence go to a fresh temporary directory.
"""

import hashlib
import json
import re
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path

from check_axiom_allowlist import ALLOWED_AXIOMS, parse_axiom_report, validate_axioms

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "docs/research/2026-08-30-carlson-half-range-verification.json"
# Ordered list from the original complete checkpoint, commit 64417646.
TARGETS_SHA256 = "6834bca044526afba7cd5fd4c3145d24cf3852abc8eeef0f0ed29466799b2084"


def load_targets(root):
    targets = json.loads((root / MANIFEST).read_text())["lean"]["targets"]
    if (not isinstance(targets, list) or len(targets) != 152
            or not all(isinstance(t, str) and re.fullmatch(r"Test\.[A-Za-z0-9_]+", t)
                       for t in targets)
            or len(set(targets)) != 152
            or hashlib.sha256("\n".join(targets).encode()).hexdigest() != TARGETS_SHA256):
        raise ValueError("target manifest differs from the frozen 152-module checkpoint")
    return targets


def audit_traces(root, targets):
    reports = {}
    errors = []
    report_count = 0
    if not targets:
        errors.append("empty target list")
    for module in targets:
        source = Path(module.replace(".", "/") + ".lean")
        trace = root / ".lake/build/lib/lean" / source.with_suffix(".trace")
        try:
            data = json.loads(trace.read_text())
            expected = re.findall(r"^#print axioms (\S+)", (root / source).read_text(), re.M)
            local = {}
            for item in data["log"]:
                parsed = parse_axiom_report(item["message"])
                report_count += len(parsed)
                for name, axioms in parsed.items():
                    local.setdefault(name, set()).update(axioms)
            for name in expected:
                if not any(actual == name or actual.endswith("." + name) for actual in local):
                    errors.append(f"{module}: missing axiom report for {name}")
            for name, axioms in local.items():
                reports.setdefault(name, set()).update(axioms)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            errors.append(f"{module}: invalid or missing source/trace: {exc}")
    errors.extend(validate_axioms(
        reports, expected_declarations=reports, allowed_axioms=ALLOWED_AXIOMS,
    ))
    if not reports:
        errors.append("no axiom reports found")
    return {
        "targets": len(targets),
        "reports": report_count,
        "unique_declarations": len(reports),
        "allowed": sorted(ALLOWED_AXIOMS),
        "observed": sorted(set().union(*reports.values())),
        "errors": errors,
    }


def source_fingerprint(root):
    """Hash source names and bytes, including untracked source additions."""
    paths = subprocess.check_output([
        "git", "ls-files", "--cached", "--others", "--exclude-standard", "-z", "--",
        "*.lean", "*.py", "lean-toolchain", "lake-manifest.json", MANIFEST,
    ], cwd=root).split(b"\0")
    digest = hashlib.sha256()
    for raw in sorted(set(paths) - {b""}):
        digest.update(raw + b"\0")
        digest.update((root / raw.decode()).read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def main():
    targets = load_targets(ROOT)
    output_dir = Path(tempfile.mkdtemp(prefix="carlson-checkpoint-"))
    command = ["nice", "-n", "15", "lake", "build", *targets]
    before = source_fingerprint(ROOT)
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    print(f"[carlson-checkpoint] building {len(targets)} targets; logs: {output_dir}", flush=True)
    with (output_dir / "lake-build.log").open("w") as log:
        build = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    evidence = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_head": head,
        "source_fingerprint_sha256": before,
        "source_fingerprint_scope": "all tracked or untracked nonignored Lean/Python files, toolchain, Lake manifest and frozen target manifest",
        "target_manifest": MANIFEST,
        "target_manifest_sha256": TARGETS_SHA256,
        "command": command,
        "build_exit_code": build.returncode,
        "scope": "152 frozen branch contracts and transitive dependencies; not repository-wide baseline",
    }
    errors = []
    if build.returncode == 0:
        audit = audit_traces(ROOT, targets)
        evidence["axiom_audit"] = audit
        errors.extend(audit["errors"])
    if source_fingerprint(ROOT) != before:
        errors.append("source changed during verification")
    evidence["errors"] = errors
    evidence["exit_code"] = build.returncode or int(bool(errors))
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)",
                      (output_dir / "lake-build.log").read_text())
    if jobs:
        evidence["build_jobs"] = int(jobs[-1])
    report = output_dir / "verification.json"
    report.write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in evidence.items() if k != "command"}, indent=2))
    print(f"[carlson-checkpoint] report: {report}")
    return evidence["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())

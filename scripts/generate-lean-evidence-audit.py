from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPOSITORY_ROOT / "archive" / "manifest.json"
OUTPUT_PATH = (
    REPOSITORY_ROOT
    / "formal"
    / "SquarePackingArchive"
    / "ManifestEvidence.lean"
)
ARTIFACT_PATTERN = re.compile(
    r"^formal/(SquarePackingArchive(?:/[A-Za-z0-9_]+)*)\.lean$"
)
THEOREM_PATTERN = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


def lean_evidence(manifest: dict[str, Any]) -> tuple[dict[str, Any], ...]:
    return tuple(
        evidence
        for claim in manifest["claims"]
        for evidence in claim["evidence"]
        if evidence["kind"] == "lean-proof"
    )


def module_name(artifact: str) -> str:
    match = ARTIFACT_PATTERN.fullmatch(artifact)
    if match is None:
        raise ValueError(f"invalid Lean artifact path: {artifact}")
    return match.group(1).replace("/", ".")


def theorem_name(evidence: dict[str, Any]) -> str:
    theorem = evidence.get("theorem")
    if not isinstance(theorem, str) or THEOREM_PATTERN.fullmatch(theorem) is None:
        raise ValueError(f"invalid Lean theorem name: {theorem}")
    if evidence.get("status") != "lean-checked":
        raise ValueError(f"Lean evidence must be lean-checked: {theorem}")
    return theorem


def render(manifest: dict[str, Any]) -> str:
    evidence = lean_evidence(manifest)
    modules = sorted({module_name(item.get("artifact", "")) for item in evidence})
    theorems = sorted({theorem_name(item) for item in evidence})
    imports = "\n".join(f"import {module}" for module in modules)
    checks = "\n".join(f"#check {theorem}" for theorem in theorems)
    return f"{imports}\n\n{checks}\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    manifest = json.loads(MANIFEST_PATH.read_text())
    generated = render(manifest)
    if arguments.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_text() != generated:
            raise SystemExit(
                "Lean evidence audit is stale; run "
                "python3 scripts/generate-lean-evidence-audit.py"
            )
        return
    OUTPUT_PATH.write_text(generated)
    print(OUTPUT_PATH.relative_to(REPOSITORY_ROOT))


if __name__ == "__main__":
    main()

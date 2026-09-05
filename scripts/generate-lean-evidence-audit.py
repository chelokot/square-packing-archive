from __future__ import annotations

import argparse
import json
import math
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


def lean_evidence(
    manifest: dict[str, Any],
) -> tuple[tuple[dict[str, Any], dict[str, Any]], ...]:
    return tuple(
        (claim, evidence)
        for claim in manifest["claims"]
        for evidence in claim["evidence"]
        if evidence["kind"] == "lean-proof"
    )


def module_name(artifact: str) -> str:
    match = ARTIFACT_PATTERN.fullmatch(artifact)
    if match is None:
        raise ValueError(f"invalid Lean artifact path: {artifact}")
    return match.group(1).replace("/", ".")


def proof_theorem_name(proof: dict[str, Any]) -> str:
    theorem = proof.get("theorem")
    if not isinstance(theorem, str) or THEOREM_PATTERN.fullmatch(theorem) is None:
        raise ValueError(f"invalid Lean theorem name: {theorem}")
    return theorem


def theorem_name(evidence: dict[str, Any]) -> str:
    theorem = proof_theorem_name(evidence)
    if evidence.get("status") != "lean-checked":
        raise ValueError(f"Lean evidence must be lean-checked: {theorem}")
    return theorem


def expected_type(claim: dict[str, Any]) -> str:
    relation = claim["relation"]
    predicate = {
        "exact": "SquarePackingArchive.IsMinimumSide",
        "lower": "SquarePackingArchive.IsLowerBound",
        "upper": "SquarePackingArchive.HasPacking",
    }[relation]
    value = claim["value"].get("lean")
    if not isinstance(value, str) or not value or any(
        forbidden in value for forbidden in ("\n", "\r", ";", "#")
    ):
        raise ValueError(f"invalid Lean value for {claim['id']}: {value}")
    return f"{predicate} {claim['n']} ({value})"


def render(manifest: dict[str, Any]) -> str:
    evidence = lean_evidence(manifest)
    modules = {module_name(item.get("artifact", "")) for _, item in evidence}
    baseline_checks = ""
    if "gridBaseline" in manifest:
        policy = manifest["gridBaseline"]
        through = policy["through"]
        if type(through) is not int or through < 1:
            raise ValueError(f"invalid grid baseline count: {through}")
        proof = policy["proof"]
        modules.add(module_name(proof.get("artifact", "")))
        theorem = proof_theorem_name(proof)
        baseline_checks = "\n\n".join(
            f"example : SquarePackingArchive.HasPacking {count} {side} := by\n"
            f"  simpa using {theorem} (count := {count}) (side := {side}) (by norm_num)"
            for count, side in (
                (count, math.isqrt(count - 1) + 1)
                for count in range(1, through + 1)
            )
        )
    imports = "\n".join(f"import {module}" for module in sorted(modules))
    checks = "\n\n".join(
        f"example : {expected_type(claim)} :=\n  {theorem_name(item)}"
        for claim, item in evidence
    )
    grids = [reference for reference in manifest["configurations"]
             if reference.get("recipe") == "grid"]
    grid_checks = "\n\n".join(
        f"example : SquarePackingArchive.HasPacking {reference['n']} {reference['side']} := by\n"
        f"  simpa using SquarePackingArchive.HasPacking.mono (targetCount := {reference['n']}) (SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking {reference['side']}) (by norm_num)"
        for reference in grids
    )
    if grid_checks:
        checks += "\n\n" + grid_checks
    if baseline_checks:
        checks += "\n\n" + baseline_checks
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

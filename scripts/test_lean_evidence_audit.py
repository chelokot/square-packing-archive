import copy
import math
from pathlib import Path
import re
import runpy
import unittest


generator = runpy.run_path(str(Path(__file__).with_name("generate-lean-evidence-audit.py")))
GRID_POLICY = {
    "through": 100,
    "proof": {
        "source": "archive-research-2026",
        "artifact": "formal/SquarePackingArchive/Records/GridBounds.lean",
        "theorem": "SquarePackingArchive.Records.GridBounds.grid_hasPacking",
        "checkedAt": "2026-09-05",
    },
}


class LeanEvidenceAuditTests(unittest.TestCase):
    def test_baseline_is_optional(self):
        self.assertEqual(generator["render"]({"claims": [], "configurations": []}), "\n\n\n")

    def test_every_baseline_has_a_typed_capacity_check(self):
        output = generator["render"]({"claims": [], "configurations": [], "gridBaseline": GRID_POLICY})
        examples = re.findall(r"example : SquarePackingArchive.HasPacking (\d+) (\d+) :=", output)
        self.assertEqual(examples, [(str(count), str(math.isqrt(count - 1) + 1))
                                   for count in range(1, 101)])
        self.assertEqual(output.count("import SquarePackingArchive.Records.GridBounds\n"), 1)
        self.assertIn("example : SquarePackingArchive.HasPacking 1 1 := by\n  simpa using", output)
        for count in range(1, 101):
            side = math.isqrt(count - 1) + 1
            self.assertIn(f"{GRID_POLICY['proof']['theorem']} (count := {count}) (side := {side}) (by norm_num)", output)
            self.assertLessEqual(count, side * side)
            self.assertLess((side - 1) * (side - 1), count)

    def test_baseline_uses_the_policy_proof_reference(self):
        policy = copy.deepcopy(GRID_POLICY)
        policy["through"] = 5
        policy["proof"]["artifact"] = "formal/SquarePackingArchive/Records/AlternateGrid.lean"
        policy["proof"]["theorem"] = "SquarePackingArchive.Records.AlternateGrid.packing"
        output = generator["render"]({"claims": [], "configurations": [], "gridBaseline": policy})
        self.assertIn("import SquarePackingArchive.Records.AlternateGrid\n", output)
        self.assertNotIn("GridBounds", output)
        self.assertEqual(output.count("example :"), 5)
        self.assertIn("SquarePackingArchive.Records.AlternateGrid.packing (count := 5) (side := 3)", output)

    def test_existing_evidence_and_explicit_grid_checks_remain(self):
        proof = dict(GRID_POLICY["proof"], kind="lean-proof", status="lean-checked")
        proof["theorem"] = "SquarePackingArchive.Records.SquareNumbers.s4_eq_two"
        manifest = {
            "claims": [{"id": "test-exact", "relation": "exact", "n": 4,
                        "value": {"lean": "2"}, "evidence": [proof]}],
            "configurations": [{"recipe": "grid", "n": 4, "side": 2}],
            "gridBaseline": GRID_POLICY,
        }
        output = generator["render"](manifest)
        self.assertEqual(output.count("import SquarePackingArchive.Records.GridBounds\n"), 1)
        self.assertIn("example : SquarePackingArchive.IsMinimumSide 4 (2) :=\n  " + proof["theorem"], output)
        self.assertIn("SquarePackingArchive.HasPacking.mono (targetCount := 4)", output)
        self.assertEqual(output.count("example :"), 102)

    def test_invalid_baseline_limits_are_rejected(self):
        for through in (0, -1, 1.5, True, "100"):
            with self.subTest(through=through):
                policy = dict(GRID_POLICY, through=through)
                with self.assertRaisesRegex(ValueError, "invalid grid baseline count"):
                    generator["render"]({"claims": [], "configurations": [], "gridBaseline": policy})

    def test_invalid_baseline_proof_references_are_rejected(self):
        for key, value in (("artifact", "../GridBounds.lean"), ("theorem", "proof\naxiom escape : False")):
            with self.subTest(key=key):
                policy = copy.deepcopy(GRID_POLICY)
                policy["proof"][key] = value
                with self.assertRaises(ValueError):
                    generator["render"]({"claims": [], "configurations": [], "gridBaseline": policy})


if __name__ == "__main__":
    unittest.main()

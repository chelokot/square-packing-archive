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
    def test_every_catalog_claim_requires_its_own_lean_proof(self):
        for active in (True, False):
            for kind, status in (("published-proof", "published"),
                                 ("interval-certificate", "computationally-checked"),
                                 ("tracker-record", "reported")):
                with self.subTest(active=active, kind=kind):
                    claim = {"id": "pending-result", "active": active,
                             "evidence": [{"kind": kind, "status": status}]}
                    with self.assertRaisesRegex(ValueError, "pending-result: catalog claims require a Lean proof"):
                        generator["render"]({"claims": [claim], "configurations": []})

    def test_a_verified_claim_does_not_hide_an_unformalized_historical_claim(self):
        checked = {"id": "checked-result", "evidence": [
            dict(GRID_POLICY["proof"], kind="lean-proof", status="lean-checked")
        ]}
        pending = {"id": "historical-result", "active": False, "evidence": []}
        with self.assertRaisesRegex(ValueError, "historical-result: catalog claims require a Lean proof"):
            generator["render"]({"claims": [checked, pending], "configurations": []})

    def test_a_lean_label_still_requires_valid_status_artifact_theorem_and_target(self):
        valid = {"id": "example-result", "n": 4, "relation": "exact",
                 "value": {"lean": "2"}, "evidence": [dict(
                     GRID_POLICY["proof"], kind="lean-proof", status="lean-checked")], "active": False}
        for field, value in (("status", "published"), ("artifact", "paper.pdf"),
                             ("theorem", "not a theorem")):
            with self.subTest(field=field):
                claim = copy.deepcopy(valid)
                claim["evidence"][0][field] = value
                with self.assertRaises(ValueError):
                    generator["render"]({"claims": [claim], "configurations": []})
        missing_target = dict(valid, value={})
        with self.assertRaisesRegex(ValueError, "invalid Lean value"):
            generator["render"]({"claims": [missing_target], "configurations": []})

    def test_baseline_is_optional(self):
        self.assertEqual(generator["render"]({"claims": [], "configurations": []}),
                         "import SquarePackingArchive.EvidenceAudit\n\n\n\n\n")

    def test_axiom_policy_covers_every_linked_proof_including_inactive_claims(self):
        proofs = [dict(GRID_POLICY["proof"], kind="lean-proof", status="lean-checked",
                       theorem=f"SquarePackingArchive.Records.Example.proof{index}")
                  for index in range(3)]
        manifest = {
            "claims": [
                {"id": "current", "n": 4, "relation": "exact", "value": {"lean": "2"},
                 "active": True, "evidence": proofs[:2]},
                {"id": "historical", "n": 4, "relation": "upper", "value": {"lean": "2"},
                 "active": False, "evidence": proofs[2:]},
            ],
            "configurations": [{"recipe": "grid", "n": 4, "side": 2}],
            "gridBaseline": GRID_POLICY,
        }
        output = generator["render"](manifest)
        audited = re.findall(r"^assert_standard_axioms (.+)$", output, re.MULTILINE)
        self.assertEqual(set(audited), {
            *(proof["theorem"] for proof in proofs), GRID_POLICY["proof"]["theorem"],
            "SquarePackingArchive.HasPacking.mono",
            "SquarePackingArchive.Records.SquareNumbers.squareNumber_hasPacking",
        })
        self.assertEqual(len(audited), len(set(audited)))

    def test_each_claim_is_checked_at_its_own_count_relation_and_exact_value(self):
        for relation, predicate in (("upper", "HasPacking"),
                                    ("lower", "IsLowerBound"),
                                    ("exact", "IsMinimumSide")):
            with self.subTest(relation=relation):
                claim = {
                    "id": "historical", "n": 10, "relation": relation,
                    "value": {"lean": "3 + Real.sqrt 2 / 2"}, "active": False,
                    "evidence": [dict(GRID_POLICY["proof"], kind="lean-proof", status="lean-checked")],
                }
                output = generator["render"]({"claims": [claim], "configurations": []})
                self.assertIn(f"example : SquarePackingArchive.{predicate} 10 (3 + Real.sqrt 2 / 2) :=", output)

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

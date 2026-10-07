import copy
from pathlib import Path
import re
import runpy
import unittest


generator = runpy.run_path(str(Path(__file__).with_name("generate-lean-evidence-audit.py")))
LEAN_PROOF = {
    "source": "archive-research-2026",
    "artifact": "formal/SquarePackingArchive/Records/SquareNumbers.lean",
    "theorem": "SquarePackingArchive.Records.SquareNumbers.s16_eq_four",
    "checkedAt": "2026-09-05",
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
                    with self.assertRaisesRegex(ValueError, "pending-result: catalog claims require a Lean or Bend proof"):
                        generator["render"]({"claims": [claim], "configurations": []})

    def test_a_claim_proved_in_bend_is_left_to_the_bend_manifest(self):
        claim = {"id": "bend-result", "evidence": [
            {"kind": "bend-proof", "status": "bend-checked", "artifact": "bend/MANIFEST.bend"}
        ]}
        audit = generator["render"]({"claims": [claim], "configurations": []})
        self.assertNotIn("bend-result", audit)
        self.assertNotIn("example", audit)

    def test_a_verified_claim_does_not_hide_an_unformalized_historical_claim(self):
        checked = {"id": "checked-result", "evidence": [
            dict(LEAN_PROOF, kind="lean-proof", status="lean-checked")
        ]}
        pending = {"id": "historical-result", "active": False, "evidence": []}
        with self.assertRaisesRegex(ValueError, "historical-result: catalog claims require a Lean or Bend proof"):
            generator["render"]({"claims": [checked, pending], "configurations": []})

    def test_a_lean_label_still_requires_valid_status_artifact_theorem_and_target(self):
        valid = {"id": "example-result", "n": 4, "relation": "exact",
                 "value": {"lean": "2"}, "evidence": [dict(
                     LEAN_PROOF, kind="lean-proof", status="lean-checked")], "active": False}
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

    def test_an_empty_catalog_audits_nothing(self):
        self.assertEqual(generator["render"]({"claims": [], "configurations": []}),
                         "import SquarePackingArchive.EvidenceAudit\n\n\n\n\n")

    def test_axiom_policy_covers_every_linked_proof_including_inactive_claims(self):
        proofs = [dict(LEAN_PROOF, kind="lean-proof", status="lean-checked",
                       theorem=f"SquarePackingArchive.Records.Example.proof{index}")
                  for index in range(3)]
        manifest = {
            "claims": [
                {"id": "current", "n": 4, "relation": "exact", "value": {"lean": "2"},
                 "active": True, "evidence": proofs[:2]},
                {"id": "historical", "n": 4, "relation": "upper", "value": {"lean": "2"},
                 "active": False, "evidence": proofs[2:]},
            ],
            "configurations": [],
        }
        output = generator["render"](manifest)
        audited = re.findall(r"^assert_standard_axioms (.+)$", output, re.MULTILINE)
        self.assertEqual(set(audited), {proof["theorem"] for proof in proofs})
        self.assertEqual(len(audited), len(set(audited)))

    def test_each_claim_is_checked_at_its_own_count_relation_and_exact_value(self):
        for relation, predicate in (("upper", "HasPacking"),
                                    ("lower", "IsLowerBound"),
                                    ("exact", "IsMinimumSide")):
            with self.subTest(relation=relation):
                claim = {
                    "id": "historical", "n": 10, "relation": relation,
                    "value": {"lean": "3 + Real.sqrt 2 / 2"}, "active": False,
                    "evidence": [dict(LEAN_PROOF, kind="lean-proof", status="lean-checked")],
                }
                output = generator["render"]({"claims": [claim], "configurations": []})
                self.assertIn(f"example : SquarePackingArchive.{predicate} 10 (3 + Real.sqrt 2 / 2) :=", output)

    def test_grid_configurations_and_the_bend_grid_baseline_add_no_lean_check(self):
        proof = dict(LEAN_PROOF, kind="lean-proof", status="lean-checked")
        manifest = {
            "claims": [{"id": "test-exact", "relation": "exact", "n": 16,
                        "value": {"lean": "4"}, "evidence": [proof]}],
            "configurations": [{"recipe": "grid", "n": 16, "side": 4}],
            "gridBaseline": {"through": 100, "proof": {"source": "archive-research-2026",
                                                       "artifact": "bend/MANIFEST.bend",
                                                       "checkedAt": "2026-10-07"}},
        }
        output = generator["render"](manifest)
        self.assertEqual(output.count("example :"), 1)
        self.assertIn("example : SquarePackingArchive.IsMinimumSide 16 (4) :=\n  " + proof["theorem"], output)
        self.assertNotIn("HasPacking.mono", output)


if __name__ == "__main__":
    unittest.main()

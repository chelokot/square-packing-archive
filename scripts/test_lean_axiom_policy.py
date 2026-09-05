from pathlib import Path
import subprocess
import unittest


FORMAL_ROOT = Path(__file__).resolve().parents[1] / "formal"


class LeanAxiomPolicyTests(unittest.TestCase):
    def compile(self, source):
        return subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            input="import SquarePackingArchive.EvidenceAudit\nimport Mathlib.Tactic\n" + source,
            text=True, capture_output=True, cwd=FORMAL_ROOT, check=False,
        )

    def test_standard_axioms_are_accepted(self):
        result = self.compile("""
assert_standard_axioms propext
assert_standard_axioms Classical.choice
assert_standard_axioms Quot.sound
theorem clean : 2 + 2 = 4 := by norm_num
assert_standard_axioms clean
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_custom_axiom_is_rejected_through_transitive_dependencies(self):
        result = self.compile("""
axiom unsupported : False
theorem intermediate : False := unsupported
theorem downstream : 2 + 2 = 5 := intermediate.elim
assert_standard_axioms downstream
""")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("downstream depends on forbidden axioms: [unsupported]", result.stdout)

    def test_sorry_dependency_is_rejected(self):
        result = self.compile("""
theorem unfinished : False := by sorry
assert_standard_axioms unfinished
""")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("forbidden axioms: [sorryAx]", result.stdout)

    def test_native_evaluation_dependency_is_rejected(self):
        result = self.compile("""
theorem nativeResult : 2 + 2 = 4 := by native_decide
assert_standard_axioms nativeResult
""")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("nativeResult depends on forbidden axioms", result.stdout)
        self.assertIn("_native.native_decide", result.stdout)

    def test_missing_declaration_is_not_silently_accepted(self):
        result = self.compile("assert_standard_axioms missingDeclaration\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Unknown constant", result.stdout)


if __name__ == "__main__":
    unittest.main()

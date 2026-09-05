import runpy
import unittest
from pathlib import Path


generator = runpy.run_path(str(Path(__file__).with_name("generate-nonadjacent-covers.py")))


class NonadjacentCoverTests(unittest.TestCase):
    def test_each_corner_choice_has_the_required_number_of_distinct_points(self):
        for final, count in ((False, 14), (True, 15)):
            for choices in range(16):
                with self.subTest(final=final, choices=choices):
                    points = generator["points_for"](final, choices)
                    self.assertEqual(len(points), count)
                    self.assertEqual(len(set(points)), count)

    def test_flipping_one_choice_only_changes_its_corner(self):
        for final in (False, True):
            baseline = generator["points_for"](final, 0)
            fixed_count = len(baseline) - 4
            for corner in range(4):
                changed = generator["points_for"](final, 1 << corner)
                self.assertEqual([index for index, pair in enumerate(zip(baseline, changed))
                                  if pair[0] != pair[1]], [fixed_count + corner])

    def test_only_initial_configuration_has_holes(self):
        for choices in range(16):
            initial = generator["regions_for"](False, choices)
            final = generator["regions_for"](True, choices)
            self.assertEqual(sum(region.kind == "hole" for region in initial), 2)
            self.assertFalse(any(region.kind == "hole" for region in final))

    def test_generated_proofs_are_reproducible(self):
        root = Path(__file__).resolve().parents[1] / "formal" / "SquarePackingArchive"
        outputs = [generator["render_data"](), generator["render_aggregate"]()]
        outputs.extend(generator["render_case"](final, choices)
                       for final in (False, True) for choices in range(16))
        for module, proof in outputs:
            with self.subTest(module=module):
                self.assertEqual((root / f"{module}.lean").read_text(), proof)


if __name__ == "__main__":
    unittest.main()

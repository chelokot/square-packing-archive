import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).with_name("generate-bentz-adjacent-covers.py")
SPEC = importlib.util.spec_from_file_location("bentz_adjacent_cover", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class BentzAdjacentCoverTests(unittest.TestCase):
    def test_generated_proofs_are_reproducible(self):
        root = SCRIPT.parent.parent / "formal" / "SquarePackingArchive"
        for configuration in MODULE.CONFIGURATIONS:
            for name, proof in MODULE.render_configuration(configuration).items():
                with self.subTest(module=name):
                    self.assertEqual((root / name).read_text(), proof)

    def test_owned_points_are_common_prefix(self):
        owned = MODULE.ANCHOR_A + MODULE.ANCHOR_B
        self.assertEqual(len(owned), 10)
        for configuration in MODULE.CONFIGURATIONS:
            with self.subTest(configuration=configuration.name):
                self.assertEqual(configuration.points[:10], owned)
                self.assertEqual(len(configuration.points), len(set(configuration.points)))

    def test_r1_grid_retains_three_owned_points_and_capacity(self):
        for index, configuration in enumerate(MODULE.CONFIGURATIONS[5:]):
            with self.subTest(configuration=configuration.name):
                self.assertEqual(len(configuration.points), 22)
                self.assertEqual(configuration.points[10:12],
                    (MODULE.point("1.5", "2.36"), MODULE.point("1.5", "3.09")))
                expected_height = MODULE.rational(59, 25) + MODULE.rational(2 * (index + 1), 25)
                self.assertEqual(configuration.points[12], (MODULE.rational(1), expected_height))

    def test_repairs_preserve_the_counting_budget(self):
        configurations = {entry.name: entry for entry in MODULE.CONFIGURATIONS}
        self.assertEqual(len(configurations["AdjacentR2Left"].points), 22)
        self.assertEqual(configurations["AdjacentR2Left"].points[-1], MODULE.point("3.1", "3"))
        self.assertIn(MODULE.point(".95", "3"), configurations["AdjacentR3"].points)
        self.assertNotIn(MODULE.point("1", "3"), configurations["AdjacentR3"].points)
        self.assertIn(MODULE.point("1", "2.84"), configurations["AdjacentR107"].points)

    def test_halfplanes_pull_back_under_all_eight_symmetries(self):
        planes = (
            MODULE.Halfplane(MODULE.rational(1, 3), MODULE.rational(-2, 5), MODULE.rational(7, 11)),
            MODULE.Halfplane(MODULE.rational(-3, 2), MODULE.rational(4, 7), MODULE.rational(-8, 3)),
        )
        for transform in range(8):
            for coordinates in (MODULE.point(".7", "2.553"), MODULE.point("3.125", ".65")):
                for plane in planes:
                    with self.subTest(transform=transform, point=coordinates, plane=plane):
                        self.assertEqual(MODULE.original_plane(plane, transform).at(coordinates),
                            plane.at(MODULE.transformed_point(coordinates, transform)))


if __name__ == "__main__":
    unittest.main()

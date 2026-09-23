import argparse

from exact_orientation_samples import sample_cells


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate")
    arguments = parser.parse_args()
    with open(arguments.certificate) as input_file:
        denominator, atom_count, stated_mass = map(
            int, input_file.readline().split())
        atoms = [tuple(map(int, input_file.readline().split()))
                 for _ in range(atom_count)]
        cell_count = int(input_file.readline())
        cells = [tuple(map(int, input_file.readline().split()))
                 for _ in range(cell_count)]
        if input_file.read().strip():
            raise ValueError("trailing certificate data")
    weights = {(x, y): weight for x, y, weight in atoms}
    if len(weights) != atom_count:
        raise ValueError("duplicate atoms")
    if stated_mass != sum(weights.values()) or stated_mass >= 61 * denominator:
        raise ValueError("invalid total mass")
    for (x, y), weight in weights.items():
        if not (0 < x < 128 and 0 < y < 128 and weight > 0):
            raise ValueError("invalid atom")
        if weights[(128 - x, y)] != weight or weights[(y, x)] != weight:
            raise ValueError("broken D4 symmetry")
    relevant = [(x, y) for x, y, _ in atoms if x >= 53 and y >= 53]
    if max(x for x, _ in relevant) - min(x for x, _ in relevant) > 74:
        raise ValueError("horizontal event range is too small")
    if max(y for _, y in relevant) - min(y for _, y in relevant) > 74:
        raise ValueError("vertical event range is too small")
    expected_cells = sample_cells(74, 1_000_000_000_000)
    if cell_count != len(expected_cells):
        raise ValueError("wrong number of orientation cells")
    for index, (cell, expected) in enumerate(zip(cells, expected_cells)):
        sample, *bounds = expected
        values = (sample.numerator, sample.denominator, *bounds)
        if cell != values:
            raise ValueError(f"incorrect orientation cell {index}")
    print(f"atoms={atom_count} cells={cell_count} "
          f"mass={stated_mass}/{denominator} metadata_verified")


if __name__ == "__main__":
    main()

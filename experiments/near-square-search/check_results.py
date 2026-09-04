import argparse
from fractions import Fraction
import json

from exact_geometry import RationalSquare, exact_errors


def main() -> None:
    parser = argparse.ArgumentParser(description="Recheck saved candidates using exact rational arithmetic.")
    parser.add_argument("results", type=argparse.FileType("r"))
    arguments = parser.parse_args()
    metadata = json.loads(next(arguments.results))
    side = Fraction(metadata["container_side"])
    if metadata["squares"] != 62 or not 0 < side < 8:
        raise ValueError("This experiment must contain 62 unit squares in side less than 8.")
    count = 0
    successes = 0
    for line in arguments.results:
        record = json.loads(line)
        squares = tuple(
            RationalSquare(
                (Fraction(square["center"][0]), Fraction(square["center"][1])),
                Fraction(square["half_angle"]),
            )
            for square in record["candidate"]
        )
        if len(squares) != metadata["squares"]:
            raise ValueError(f"Wrong square count for seed {record['seed']}.")
        errors = exact_errors(squares, side)
        if bool(errors) == record["exact_certificate_passed"] or len(errors) != record["exact_error_count"]:
            raise ValueError(f"Certificate status mismatch for seed {record['seed']}.")
        count += 1
        successes += not errors
    if count != metadata["seeds"]:
        raise ValueError("The results file is incomplete.")
    print(f"Rechecked {count} candidates exactly: {successes} feasible packings; {count - successes} rejected.")


if __name__ == "__main__":
    main()

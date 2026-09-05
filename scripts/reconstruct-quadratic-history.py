from fractions import Fraction
import json
from pathlib import Path
import runpy


helpers = runpy.run_path(str(Path(__file__).with_name("reconstruct-quadratic-tracker.py")))
exact = helpers["exact"]
staircase = helpers["staircase"]
reflected = helpers["reflected"]
shifted = helpers["shifted"]
rotated_block = helpers["rotated_block"]


def scaled(value, factor):
    return exact(value.rational * factor, value.radical * factor)


def row_lengths(lengths):
    return [(exact(Fraction(2 * column + 1, 2)), exact(Fraction(2 * row + 1, 2)), False)
            for row, length in enumerate(lengths) for column in range(length)]


def diagonal_cells(cells, origin_x, origin_y, angle=45):
    result = []
    for local_x, local_y in cells:
        if angle == 45:
            center_x = (local_x - local_y).half_sqrt_two()
            center_y = (local_x + local_y).half_sqrt_two()
        elif angle == -45:
            center_x = (local_x + local_y).half_sqrt_two()
            center_y = (local_y - local_x).half_sqrt_two()
        elif angle == 135:
            center_x = scaled((local_x + local_y).half_sqrt_two(), -1)
            center_y = (local_x - local_y).half_sqrt_two()
        else:
            raise ValueError(f"Unsupported diagonal angle {angle}")
        result.append((origin_x + center_x, origin_y + center_y, True))
    return result


def wainwright_19():
    side = exact(3, Fraction(4, 3))
    squares = staircase(2) + reflected(staircase(3), side, True, True)
    origin_x = scaled(side, Fraction(3, 2)) - exact(3)
    origin_y = scaled(side, Fraction(1, 2)) - exact(1)
    cells = [(exact(Fraction(1, 2)), exact(Fraction(2 * row + 1, 2))) for row in range(2)]
    group = [(side - exact(Fraction(1, 2)), exact(Fraction(1, 2)), False)]
    group += diagonal_cells(cells, origin_x, origin_y, 135)
    group += diagonal_cells(cells, origin_x + exact(Fraction(7, 2), Fraction(1, 2)) - side,
                            origin_y + exact(Fraction(7, 2), Fraction(3, 2)) - side, 135)
    return side, squares + group + [(center_y, center_x, rotated) for center_x, center_y, rotated in group]


def hamalainen_11():
    side = exact(2, Fraction(4, 3))
    offset = exact(Fraction(-2, 3), 1)
    squares = staircase(1) + reflected(staircase(1), side, vertical=True)
    squares += reflected(row_lengths([2, 1, 1]), side, horizontal=True)
    cells = [(exact(Fraction(1, 2)) - offset, exact(Fraction(1, 2)))]
    cells += [(exact(Fraction(-1, 2)) - offset, exact(Fraction(2 * row + 1, 2)) - offset)
              for row in range(2)]
    squares += diagonal_cells(cells, side - exact(1), exact(3))
    squares += rotated_block(1, 2, exact(), exact(2), exact(), exact(-2))
    return side, reflected(squares, side, vertical=True)


def stenlund_68():
    side = exact(6, 2)
    corner = row_lengths([4, 4, 3, 2])
    squares = [square for horizontal in [False, True] for vertical in [False, True]
               for square in reflected(corner, side, horizontal, vertical)]
    squares += rotated_block(4, 4, exact(3), exact(3), exact(), exact(-2))
    return side, squares


def friedman_69():
    side = exact(Fraction(5, 2), Fraction(9, 2))
    corner = row_lengths([7, 4, 3, 2, 1])
    squares = corner + [(side - center_y, side - center_x, rotated)
                        for center_x, center_y, rotated in corner]
    squares += [(side - exact(Fraction(1, 2)), exact(Fraction(1, 2)), False)]
    squares += reflected(staircase(2), side, vertical=True)
    cells = [(exact(), exact(Fraction(1, 2)))]
    cells += [(exact(Fraction(2 * column + 1, 2) - 2), exact(Fraction(3, 2))) for column in [1, 2]]
    cells += [(exact(Fraction(2 * column + 1, 2) - 2), exact(Fraction(2 * row + 1, 2)))
              for row in range(2, 9) for column in range(4)]
    squares += diagonal_cells(cells, side - exact(1), exact(1))
    return side, squares


def hamalainen_17():
    side = exact(Fraction(7, 3), Fraction(5, 3))
    squares = staircase(1) + reflected(staircase(1), side, horizontal=True)
    squares += reflected(staircase(2), side, True, True)
    squares += reflected(row_lengths([2, 1, 1]), side, vertical=True)
    for count, origin_x, origin_y in [
        (3, exact(Fraction(7, 6), Fraction(1, 3)), exact(Fraction(1, 2), 2)),
        (3, exact(1), exact(Fraction(2, 3), Fraction(4, 3))),
        (2, exact(Fraction(5, 3), Fraction(-2, 3)), exact(0, 1)),
    ]:
        cells = [(exact(Fraction(2 * column + 1, 2)), exact(Fraction(1, 2))) for column in range(count)]
        squares += diagonal_cells(cells, origin_x, origin_y, -45)
    return side, reflected(squares, side, horizontal=True)


def cottingham_19():
    side = exact(Fraction(7, 2), 1)
    squares = staircase(1) + reflected(staircase(1), side, True, True)
    squares += reflected(staircase(2), side, horizontal=True)
    squares += reflected(staircase(3), side, vertical=True)
    cells = [(exact(Fraction(2 * column + 1, 2)), exact(Fraction(2 * row + 1, 2) - 2))
             for row in range(4) for column in range(2)]
    squares += diagonal_cells(cells, exact(2), side - exact(2), -45)
    return side, [(center_y, side - center_x, rotated) for center_x, center_y, rotated in squares]


def goebel_19():
    side = exact(4, Fraction(2, 3))
    squares = staircase(1) + reflected(staircase(1), side, True, True)
    squares += reflected(row_lengths([3, 3, 2]), side, horizontal=True)
    squares += reflected(row_lengths([3, 1, 1]), side, vertical=True)
    single = diagonal_cells([(exact(Fraction(-1, 2)), exact(Fraction(1, 2)))],
                            side - exact(3), scaled(side, Fraction(1, 2)) - exact(1))
    squares += single + [(side - center_y, side - center_x, rotated) for center_x, center_y, rotated in single]
    squares += rotated_block(2, 1, side - exact(Fraction(5, 2)), exact(Fraction(5, 2)), exact(-1), exact())
    return side, [(side - center_y, center_x, rotated) for center_x, center_y, rotated in squares]


def configurations():
    records = [
        (19, wainwright_19(), "square-19", "square-19-tracker", "4.88561808316412673173558496561"),
        (11, helpers["asymmetric_corners"](1, 2), "square-11_r1a", "square-11-goebel-1979", "3.91421356237309504880168872421"),
        (11, hamalainen_11(), "square-11_r2", "square-11-hamalainen-1980", "3.88561808316412673173558496561293"),
        (17, hamalainen_17(), "square-17_r2", "square-17-hamalainen-1980", "4.69035593728849174800281454035"),
        (19, goebel_19(), "square-19_r1", "square-19-goebel-1979", "4.94280904158206336586779248281"),
        (19, cottingham_19(), "square-19_r2", "square-19-cottingham-1979", "4.91421356237309504880168872421"),
        (68, stenlund_68(), "square-68_r1", "square-68-stenlund-1980", "8.82842712474619009760337744842"),
        (69, friedman_69(), "square-69_r1", "square-69-friedman-1997", "8.86396103067892771960759925894"),
    ]
    result = []
    for count, (side, squares), source, identifier, decimal in records:
        configuration = helpers["configuration"](count, side, squares, source, decimal)
        configuration["id"] = identifier
        result.append(configuration)
    return result


def main():
    directory = Path(__file__).resolve().parents[1] / "archive" / "configurations"
    for configuration in configurations():
        (directory / f"{configuration['id']}.json").write_text(json.dumps(configuration, indent=2) + "\n")


if __name__ == "__main__":
    main()

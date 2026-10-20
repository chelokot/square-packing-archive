import math
from fractions import Fraction


PRECISION = 10 ** 80


def radical_interval(coefficient_a, coefficient_b, discriminant, branch):
    radical_floor = math.isqrt(discriminant * PRECISION ** 2)
    if branch == 1:
        numerator_low = -coefficient_b * PRECISION + radical_floor
        numerator_high = numerator_low + 1
    else:
        numerator_high = -coefficient_b * PRECISION - radical_floor
        numerator_low = numerator_high - 1
    divisor = 2 * coefficient_a * PRECISION
    first = Fraction(numerator_low, divisor)
    second = Fraction(numerator_high, divisor)
    return min(first, second), max(first, second)


def event_roots(maximum_difference):
    roots = {}
    square_two_floor = math.isqrt(2 * PRECISION ** 2)
    upper_low = Fraction(square_two_floor - PRECISION, PRECISION)
    upper_high = Fraction(square_two_floor + 1 - PRECISION, PRECISION)
    for a in range(-maximum_difference, maximum_difference + 1):
        for b in range(-maximum_difference, maximum_difference + 1):
            for z in (-16, 0, 16):
                coefficient_a = -a - z
                coefficient_b = 2 * b
                coefficient_c = a - z
                if coefficient_a == 0:
                    if coefficient_b == 0:
                        continue
                    root = Fraction(-coefficient_c, coefficient_b)
                    if root > 0 and (root + 1) ** 2 < 2:
                        roots[("r", root)] = (root, root)
                    continue
                discriminant = coefficient_b ** 2 - 4 * coefficient_a * coefficient_c
                if discriminant < 0:
                    continue
                radical = math.isqrt(discriminant)
                if radical ** 2 == discriminant:
                    for sign in (-1, 1):
                        root = Fraction(-coefficient_b + sign * radical,
                                        2 * coefficient_a)
                        if root > 0 and (root + 1) ** 2 < 2:
                            roots[("r", root)] = (root, root)
                    continue
                divisor = math.gcd(coefficient_a,
                                   math.gcd(coefficient_b, coefficient_c))
                normalized = (coefficient_a // divisor,
                              coefficient_b // divisor,
                              coefficient_c // divisor)
                if normalized[0] < 0:
                    normalized = tuple(-value for value in normalized)
                for branch in (-1, 1):
                    lower, upper = radical_interval(*normalized[:2],
                                                     normalized[1] ** 2 -
                                                     4 * normalized[0] * normalized[2],
                                                     branch)
                    if lower > 0 and upper < upper_low:
                        roots[("i", *normalized, branch)] = (lower, upper)
                    elif lower < upper_high and upper > upper_low:
                        if normalized != (1, 2, -1):
                            raise ArithmeticError("unresolved root at upper endpoint")
    ordered = sorted(roots.values(), key=lambda interval: interval[0])
    for left, right in zip(ordered[:-1], ordered[1:]):
        if left[1] >= right[0]:
            raise ArithmeticError("overlapping root intervals")
    return ordered, (upper_low, upper_high)


def sample_between(lower, upper):
    midpoint = (lower + upper) / 2
    for denominator in (10 ** 6, 10 ** 8, 10 ** 10, 10 ** 12):
        candidate = midpoint.limit_denominator(denominator)
        if lower < candidate < upper:
            return candidate
    raise ArithmeticError("could not find rational sample")


def samples(maximum_difference):
    roots, endpoint = event_roots(maximum_difference)
    boundaries = [(Fraction(0), Fraction(0)), *roots, endpoint]
    return [
        sample_between(left[1], right[0])
        for left, right in zip(boundaries[:-1], boundaries[1:])
    ]


def sample_cells(maximum_difference, scale):
    roots, endpoint = event_roots(maximum_difference)
    boundaries = [(Fraction(0), Fraction(0)), *roots, endpoint]
    cells = []
    for left, right in zip(boundaries[:-1], boundaries[1:]):
        sample = sample_between(left[1], right[0])
        cells.append((sample, *cell_bounds(left[0], right[1], scale)))
    return cells


def trigonometry_bounds(left_t, right_t, scale):
    left_cosine = (1 - left_t ** 2) / (1 + left_t ** 2)
    right_cosine = (1 - right_t ** 2) / (1 + right_t ** 2)
    left_sine = 2 * left_t / (1 + left_t ** 2)
    right_sine = 2 * right_t / (1 + right_t ** 2)
    cosine_low = scale * right_cosine.numerator // right_cosine.denominator
    cosine_high = -(-scale * left_cosine.numerator // left_cosine.denominator)
    sine_low = scale * left_sine.numerator // left_sine.denominator
    sine_high = -(-scale * right_sine.numerator // right_sine.denominator)
    return cosine_low, cosine_high, sine_low, sine_high


def cell_bounds(left_t, right_t, scale):
    time_scale = 10 ** 15
    time_low = time_scale * left_t.numerator // left_t.denominator
    time_high = -(-time_scale * right_t.numerator // right_t.denominator)
    return (*trigonometry_bounds(left_t, right_t, scale), time_low, time_high)


def subdivided_cell(maximum_difference, scale, index, subdivisions,
                    segment_index=None):
    roots, endpoint = event_roots(maximum_difference)
    boundaries = [(Fraction(0), Fraction(0)), *roots, endpoint]
    left, right = boundaries[index:index + 2]
    sample = sample_between(left[1], right[0])
    indices = range(subdivisions) if segment_index is None else (segment_index,)
    cells = []
    for part in indices:
        lower = left[1] + (right[0] - left[1]) * part / subdivisions
        upper = left[1] + (right[0] - left[1]) * (part + 1) / subdivisions
        if part == 0:
            lower = left[0]
        if part + 1 == subdivisions:
            upper = right[1]
        cells.append((sample, *cell_bounds(lower, upper, scale)))
    return cells


if __name__ == "__main__":
    chosen = samples(74)
    denominators = [sample.denominator for sample in chosen]
    print(f"samples={len(chosen)} maximum_denominator={max(denominators)} "
          f"median_denominator={sorted(denominators)[len(denominators) // 2]}")

import type { ExactNumber, Ratio } from "./schema.ts";

type Fraction = Readonly<{ numerator: bigint; denominator: bigint }>;
export type Quadratic = readonly [Fraction, Fraction];

const fraction = (numerator: bigint, denominator: bigint): Fraction => {
  if (denominator <= 0n) throw new Error("Denominator must be positive");
  let divisor = numerator < 0n ? -numerator : numerator;
  let remainder = denominator;
  while (remainder !== 0n) {
    [divisor, remainder] = [remainder, divisor % remainder];
  }
  return { numerator: numerator / divisor, denominator: denominator / divisor };
};

const zeroFraction = fraction(0n, 1n);
const oneFraction = fraction(1n, 1n);
const addFraction = (left: Fraction, right: Fraction): Fraction =>
  fraction(
    left.numerator * right.denominator + right.numerator * left.denominator,
    left.denominator * right.denominator,
  );
const multiplyFraction = (left: Fraction, right: Fraction): Fraction =>
  fraction(
    left.numerator * right.numerator,
    left.denominator * right.denominator,
  );
const negateFraction = (value: Fraction): Fraction => ({
  numerator: -value.numerator,
  denominator: value.denominator,
});
const fromRatio = (value: Ratio): Fraction =>
  fraction(BigInt(value.numerator), BigInt(value.denominator));

export const exactZero: Quadratic = [zeroFraction, zeroFraction];
export const exactOne: Quadratic = [oneFraction, zeroFraction];
export const exactHalf: Quadratic = [fraction(1n, 2n), zeroFraction];

export const fromExact = (value: ExactNumber): Quadratic =>
  "numerator" in value
    ? [fromRatio(value), zeroFraction]
    : [fromRatio(value.rational), fromRatio(value.sqrtTwo)];

export const addExact = (left: Quadratic, right: Quadratic): Quadratic => [
  addFraction(left[0], right[0]),
  addFraction(left[1], right[1]),
];

export const negateExact = (value: Quadratic): Quadratic => [
  negateFraction(value[0]),
  negateFraction(value[1]),
];

export const subtractExact = (left: Quadratic, right: Quadratic): Quadratic =>
  addExact(left, negateExact(right));

export const multiplyExact = (left: Quadratic, right: Quadratic): Quadratic => [
  addFraction(
    multiplyFraction(left[0], right[0]),
    multiplyFraction(fraction(2n, 1n), multiplyFraction(left[1], right[1])),
  ),
  addFraction(
    multiplyFraction(left[0], right[1]),
    multiplyFraction(left[1], right[0]),
  ),
];

const signInteger = (value: bigint): -1 | 0 | 1 =>
  value < 0n ? -1 : value > 0n ? 1 : 0;

export const signExact = ([rational, radical]: Quadratic): -1 | 0 | 1 => {
  const rationalSign = signInteger(rational.numerator);
  const radicalSign = signInteger(radical.numerator);
  if (rationalSign === 0) return radicalSign;
  if (radicalSign === 0 || rationalSign === radicalSign) return rationalSign;
  const difference =
    rational.numerator ** 2n * radical.denominator ** 2n -
    2n * radical.numerator ** 2n * rational.denominator ** 2n;
  return signInteger(difference) === rationalSign
    ? 1
    : difference === 0n
      ? 0
      : -1;
};

export const absExact = (value: Quadratic): Quadratic =>
  signExact(value) < 0 ? negateExact(value) : value;

export const compareExact = (left: Quadratic, right: Quadratic): -1 | 0 | 1 =>
  signExact(subtractExact(left, right));

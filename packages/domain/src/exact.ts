import type { ExactNumber, Ratio } from "./schema.ts";

type Fraction = Readonly<{ numerator: bigint; denominator: bigint }>;
export type Quadratic = Readonly<{
  rational: Fraction;
  radical: Fraction;
  radicand: bigint;
}>;

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

const quadratic = (
  rational: Fraction,
  radical: Fraction,
  radicand: bigint,
): Quadratic => ({
  rational,
  radical,
  radicand: radical.numerator === 0n ? 0n : radicand,
});

export const exactZero = quadratic(zeroFraction, zeroFraction, 0n);
export const exactOne = quadratic(oneFraction, zeroFraction, 0n);
export const exactHalf = quadratic(fraction(1n, 2n), zeroFraction, 0n);

export const fromExact = (value: ExactNumber): Quadratic =>
  "numerator" in value
    ? quadratic(fromRatio(value), zeroFraction, 0n)
    : "sqrtTwo" in value
      ? quadratic(fromRatio(value.rational), fromRatio(value.sqrtTwo), 2n)
      : quadratic(
          fromRatio(value.rational),
          fromRatio(value.radical),
          BigInt(value.radicand),
        );

const sharedRadicand = (left: Quadratic, right: Quadratic): bigint => {
  if (left.radical.numerator === 0n) return right.radicand;
  if (right.radical.numerator === 0n) return left.radicand;
  if (left.radicand !== right.radicand)
    throw new Error("A configuration must use a single quadratic field");
  return left.radicand;
};

export const addExact = (left: Quadratic, right: Quadratic): Quadratic =>
  quadratic(
    addFraction(left.rational, right.rational),
    addFraction(left.radical, right.radical),
    sharedRadicand(left, right),
  );

export const negateExact = (value: Quadratic): Quadratic =>
  quadratic(
    negateFraction(value.rational),
    negateFraction(value.radical),
    value.radicand,
  );

export const subtractExact = (left: Quadratic, right: Quadratic): Quadratic =>
  addExact(left, negateExact(right));

export const multiplyExact = (left: Quadratic, right: Quadratic): Quadratic => {
  const radicand = sharedRadicand(left, right);
  return quadratic(
    addFraction(
      multiplyFraction(left.rational, right.rational),
      multiplyFraction(
        fraction(radicand, 1n),
        multiplyFraction(left.radical, right.radical),
      ),
    ),
    addFraction(
      multiplyFraction(left.rational, right.radical),
      multiplyFraction(left.radical, right.rational),
    ),
    radicand,
  );
};

const signInteger = (value: bigint): -1 | 0 | 1 =>
  value < 0n ? -1 : value > 0n ? 1 : 0;

export const signExact = ({
  rational,
  radical,
  radicand,
}: Quadratic): -1 | 0 | 1 => {
  const rationalSign = signInteger(rational.numerator);
  const radicalSign = signInteger(radical.numerator);
  if (rationalSign === 0) return radicalSign;
  if (radicalSign === 0 || rationalSign === radicalSign) return rationalSign;
  const difference =
    rational.numerator ** 2n * radical.denominator ** 2n -
    radicand * radical.numerator ** 2n * rational.denominator ** 2n;
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

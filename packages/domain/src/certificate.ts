import {
  absExact,
  addExact,
  compareExact,
  exactHalf,
  exactOne,
  exactZero,
  fromExact,
  multiplyExact,
  negateExact,
  subtractExact,
  type Quadratic,
} from "./exact.ts";
import type { PackingConfiguration } from "./schema.ts";

type Vector = readonly [Quadratic, Quadratic];
type Square = Readonly<{
  center: Vector;
  horizontal: Vector;
  vertical: Vector;
}>;

const dot = (left: Vector, right: Vector): Quadratic =>
  addExact(multiplyExact(left[0], right[0]), multiplyExact(left[1], right[1]));

const radius = (square: Square, axis: Vector): Quadratic =>
  multiplyExact(
    exactHalf,
    addExact(
      absExact(dot(square.horizontal, axis)),
      absExact(dot(square.vertical, axis)),
    ),
  );

export const validateConfigurationGeometry = (
  configuration: PackingConfiguration,
): readonly string[] => {
  const errors: string[] = [];
  const side = fromExact(configuration.containerSide);
  const containmentMargin = fromExact(
    configuration.certificate.minimumContainmentMargin,
  );
  const separationMargin = fromExact(
    configuration.certificate.minimumSeparationMargin,
  );
  if (compareExact(fromExact(configuration.squareSide), exactOne) !== 0)
    errors.push("Squares must have unit side length");
  if (compareExact(side, exactZero) <= 0)
    errors.push("Container side must be positive");
  if (
    compareExact(containmentMargin, exactZero) < 0 ||
    compareExact(separationMargin, exactZero) < 0
  )
    errors.push("Certificate margins must be nonnegative");
  if (
    new Set(configuration.squares.map(({ id }) => id)).size !== configuration.n
  )
    errors.push("Square ids must be distinct and match the square count");
  const squares: Square[] = configuration.squares.map((square) => {
    const cosine = fromExact(square.orientation.cosine);
    const sine = fromExact(square.orientation.sine);
    const tangent = fromExact(square.orientation.tangentHalfAngle);
    if (
      compareExact(
        addExact(multiplyExact(cosine, cosine), multiplyExact(sine, sine)),
        exactOne,
      ) !== 0
    )
      errors.push(`Square ${square.id}: frame is not unit length`);
    const tangentSquared = multiplyExact(tangent, tangent);
    const denominator = addExact(exactOne, tangentSquared);
    if (
      compareExact(
        multiplyExact(cosine, denominator),
        subtractExact(exactOne, tangentSquared),
      ) !== 0 ||
      compareExact(
        multiplyExact(sine, denominator),
        addExact(tangent, tangent),
      ) !== 0
    )
      errors.push(
        `Square ${square.id}: tangent-half-angle does not match frame`,
      );
    const extent = multiplyExact(
      exactHalf,
      addExact(absExact(cosine), absExact(sine)),
    );
    const center: Vector = [
      fromExact(square.center.x),
      fromExact(square.center.y),
    ];
    for (const coordinate of center) {
      if (
        compareExact(subtractExact(coordinate, extent), containmentMargin) <
          0 ||
        compareExact(
          subtractExact(subtractExact(side, coordinate), extent),
          containmentMargin,
        ) < 0
      )
        errors.push(`Square ${square.id}: containment certificate failed`);
    }
    return {
      center,
      horizontal: [cosine, sine],
      vertical: [negateExact(sine), cosine],
    };
  });
  for (let first = 0; first < squares.length; first++) {
    for (let second = first + 1; second < squares.length; second++) {
      const left = squares[first]!;
      const right = squares[second]!;
      const displacement: Vector = [
        subtractExact(right.center[0], left.center[0]),
        subtractExact(right.center[1], left.center[1]),
      ];
      const separated = [
        left.horizontal,
        left.vertical,
        right.horizontal,
        right.vertical,
      ].some(
        (axis) =>
          compareExact(
            subtractExact(
              subtractExact(
                absExact(dot(displacement, axis)),
                radius(left, axis),
              ),
              radius(right, axis),
            ),
            separationMargin,
          ) >= 0,
      );
      if (!separated)
        errors.push(
          `Squares ${configuration.squares[first]!.id}, ${configuration.squares[second]!.id}: separation certificate failed`,
        );
    }
  }
  return errors;
};

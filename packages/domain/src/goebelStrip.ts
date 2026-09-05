import { compareExact, fromExact } from "./exact.ts";
import type { ExactNumber, PackingConfiguration, Ratio } from "./schema.ts";

const ratio = (numerator: number, denominator = 1): Ratio => ({
  numerator: String(numerator),
  denominator: String(denominator),
});

const quadratic = (
  rationalNumerator: number,
  rationalDenominator: number,
  radicalNumerator: number,
  radicalDenominator: number,
): ExactNumber => ({
  rational: ratio(rationalNumerator, rationalDenominator),
  sqrtTwo: ratio(radicalNumerator, radicalDenominator),
});

export const goebelStripConfiguration = (
  id: string,
  steps: number,
  stripCount: number,
  importedAt: string,
): PackingConfiguration => {
  const count = steps * (steps + 1) + 2 + stripCount;
  if (
    !Number.isSafeInteger(steps) ||
    steps < 1 ||
    !Number.isSafeInteger(stripCount) ||
    stripCount < 1 ||
    !Number.isSafeInteger(count)
  ) {
    throw new Error("A Göbel strip needs positive integer dimensions");
  }
  if (
    compareExact(
      fromExact(quadratic(0, 1, stripCount - 1, 2)),
      fromExact(ratio(steps - 1)),
    ) > 0
  ) {
    throw new Error("The rotated strip is too long for these staircases");
  }

  const axisOrientation = {
    tangentHalfAngle: ratio(0),
    cosine: ratio(1),
    sine: ratio(0),
    angleRadiansApprox: 0,
  };
  const stripOrientation = {
    tangentHalfAngle: quadratic(-1, 1, 1, 1),
    cosine: quadratic(0, 1, 1, 2),
    sine: quadratic(0, 1, 1, 2),
    angleRadiansApprox: Math.PI / 4,
  };
  const staircaseCount = steps * (steps + 1);
  const staircases = Array.from({ length: staircaseCount }, (_, index) => {
    const column = Math.floor(index / (steps + 1));
    const row = index % (steps + 1);
    return {
      id: index,
      center:
        column + row < steps
          ? { x: ratio(2 * column + 1, 2), y: ratio(2 * row + 1, 2) }
          : {
              x: quadratic(2 * column + 3, 2, 1, 2),
              y: quadratic(2 * row + 1, 2, 1, 2),
            },
      orientation: axisOrientation,
    };
  });
  const low = ratio(1, 2);
  const high = quadratic(2 * steps + 1, 2, 1, 2);
  const corners = [
    {
      id: staircaseCount,
      center: { x: high, y: low },
      orientation: axisOrientation,
    },
    {
      id: staircaseCount + 1,
      center: { x: low, y: high },
      orientation: axisOrientation,
    },
  ];
  const strip = Array.from({ length: stripCount }, (_, index) => ({
    id: staircaseCount + 2 + index,
    center: {
      x: quadratic(steps + 1, 2, stripCount - 2 * index, 4),
      y: quadratic(steps + 1, 2, 2 * index - stripCount + 2, 4),
    },
    orientation: stripOrientation,
  }));
  const decimal = String(steps + 1 + Math.SQRT1_2);
  return {
    schemaVersion: 1,
    id,
    n: count,
    containerSide: {
      rational: ratio(steps + 1),
      sqrtTwo: ratio(1, 2),
      decimal,
    },
    coordinateSystem: "physical-cartesian-bottom-left",
    squareSide: ratio(1),
    squares: [...staircases, ...corners, ...strip],
    certificate: {
      method: "exact-quadratic-separating-axis",
      minimumContainmentMargin: ratio(0),
      minimumSeparationMargin: ratio(0),
      orientationReconstruction:
        "Exact coordinates in Q(√2); strip squares have cosine = sine = √2/2",
    },
    provenance: {
      source:
        "formal/SquarePackingArchive/Records/GoebelStrip.lean#goebel_strip_hasPacking",
      sourceOptimizedContainerSide: decimal,
      importedAt,
    },
  };
};

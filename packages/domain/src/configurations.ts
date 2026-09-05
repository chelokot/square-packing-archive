import type { ExactNumber, PackingConfiguration, Ratio } from "./schema.ts";

const ratio = (numerator: number, denominator = 1): Ratio => ({
  numerator: String(numerator),
  denominator: String(denominator),
});

export const gridConfiguration = (
  id: string,
  count: number,
  side: number,
  importedAt: string,
) => {
  if (
    !Number.isSafeInteger(count) ||
    count < 1 ||
    !Number.isSafeInteger(side) ||
    side < 1 ||
    count > side * side
  ) {
    throw new Error(
      "A grid needs positive integer dimensions and sufficient capacity",
    );
  }
  return {
    schemaVersion: 1,
    id,
    n: count,
    containerSide: { ...ratio(side), decimal: String(side) },
    coordinateSystem: "physical-cartesian-bottom-left",
    squareSide: ratio(1),
    squares: Array.from({ length: count }, (_, index) => ({
      id: index,
      center: {
        x: ratio(2 * Math.floor(index / side) + 1, 2),
        y: ratio(2 * (index % side) + 1, 2),
      },
      orientation: {
        tangentHalfAngle: ratio(0),
        cosine: ratio(1),
        sine: ratio(0),
        angleRadiansApprox: 0,
      },
    })),
    certificate: {
      method: "exact-rational-separating-axis",
      minimumContainmentMargin: ratio(0),
      minimumSeparationMargin: ratio(0),
      orientationReconstruction: "Axis-aligned grid: cosine = 1, sine = 0",
    },
    provenance: {
      source:
        "formal/SquarePackingArchive/Records/SquareNumbers.lean#gridPacking",
      sourceOptimizedContainerSide: String(side),
      importedAt,
    },
  } satisfies PackingConfiguration;
};

export const goebelConfiguration = (
  id: string,
  count: 5 | 10,
  importedAt: string,
): PackingConfiguration => {
  const quadratic = (rational: Ratio, sqrtTwo: Ratio): ExactNumber => ({
    rational,
    sqrtTwo,
  });
  const low = ratio(1, 2);
  const high = quadratic(ratio(3, 2), ratio(1, 2));
  const middle = quadratic(ratio(1), ratio(1, 4));
  const extension = quadratic(ratio(5, 2), ratio(1, 2));
  const diagonal = quadratic(ratio(0), ratio(1, 2));
  const centers: readonly (readonly [ExactNumber, ExactNumber])[] = [
    [low, low],
    [high, low],
    [low, high],
    [high, high],
    [middle, middle],
    ...(count === 10
      ? ([
          [low, extension],
          [ratio(3, 2), extension],
          [ratio(5, 2), extension],
          [extension, low],
          [extension, ratio(3, 2)],
        ] as const)
      : []),
  ];
  const decimal = count === 5 ? "2.70710678118654" : "3.70710678118654";
  return {
    schemaVersion: 1,
    id,
    n: count,
    containerSide: {
      rational: ratio(count === 5 ? 2 : 3),
      sqrtTwo: ratio(1, 2),
      decimal,
    },
    coordinateSystem: "physical-cartesian-bottom-left",
    squareSide: ratio(1),
    squares: centers.map(([x, y], index) => ({
      id: index,
      center: { x, y },
      orientation:
        index === 4
          ? {
              tangentHalfAngle: quadratic(ratio(-1), ratio(1)),
              cosine: diagonal,
              sine: diagonal,
              angleRadiansApprox: Math.PI / 4,
            }
          : {
              tangentHalfAngle: ratio(0),
              cosine: ratio(1),
              sine: ratio(0),
              angleRadiansApprox: 0,
            },
    })),
    certificate: {
      method: "exact-quadratic-separating-axis",
      minimumContainmentMargin: ratio(0),
      minimumSeparationMargin: ratio(0),
      orientationReconstruction:
        "Exact coordinates in Q(√2); the central square has cosine = sine = √2/2",
    },
    provenance: {
      source: `formal/SquarePackingArchive/Records/Square${count}.lean#s${count}_le_goebel`,
      sourceOptimizedContainerSide: decimal,
      importedAt,
    },
  };
};

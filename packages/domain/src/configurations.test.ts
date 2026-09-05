import { describe, expect, test } from "bun:test";
import { gridConfiguration } from "./configurations.ts";
import { packingConfigurationSchema } from "./schema.ts";

describe("grid coordinates", () => {
  test("every count from 1 to 100 has exact contained, nonoverlapping unit squares", () => {
    for (let count = 1; count <= 100; count++) {
      const side = Math.ceil(Math.sqrt(count));
      const configuration = gridConfiguration(
        `square-${count}-grid`,
        count,
        side,
        "2026-09-05",
      );
      expect(
        packingConfigurationSchema.safeParse(configuration).success,
      ).toBeTrue();
      expect(configuration.squares).toHaveLength(count);
      const centers = configuration.squares.map(({ center }) => ({
        x: BigInt(center.x.numerator),
        y: BigInt(center.y.numerator),
      }));
      for (const center of centers) {
        expect(center.x >= 1n && center.x <= BigInt(2 * side - 1)).toBeTrue();
        expect(center.y >= 1n && center.y <= BigInt(2 * side - 1)).toBeTrue();
      }
      for (let first = 0; first < count; first++) {
        for (let second = first + 1; second < count; second++) {
          const horizontal = centers[first]!.x - centers[second]!.x;
          const vertical = centers[first]!.y - centers[second]!.y;
          expect(
            horizontal >= 2n ||
              horizontal <= -2n ||
              vertical >= 2n ||
              vertical <= -2n,
          ).toBeTrue();
        }
      }
    }
  });

  test("matches the column-major ordering of Lean gridPacking", () => {
    const configuration = gridConfiguration(
      "square-6-grid",
      6,
      3,
      "2026-09-05",
    );
    expect(
      configuration.squares.map(({ center }) => [
        center.x.numerator,
        center.y.numerator,
      ]),
    ).toEqual([
      ["1", "1"],
      ["1", "3"],
      ["1", "5"],
      ["3", "1"],
      ["3", "3"],
      ["3", "5"],
    ]);
  });

  test.each([
    [0, 3],
    [6, 2],
    [6.5, 3],
    [6, 2.5],
  ])("rejects count %s and side %s", (count, side) => {
    expect(() =>
      gridConfiguration("invalid", count, side, "2026-09-05"),
    ).toThrow();
  });
});

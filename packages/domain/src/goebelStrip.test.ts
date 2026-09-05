import { describe, expect, test } from "bun:test";
import { validateConfigurationGeometry } from "./certificate.ts";
import { goebelStripConfiguration } from "./goebelStrip.ts";
import { packingConfigurationSchema } from "./schema.ts";

describe("Göbel strip coordinates", () => {
  test.each([
    [1, 1, 5],
    [2, 2, 10],
    [3, 3, 17],
    [4, 5, 27],
    [5, 6, 38],
    [6, 8, 52],
    [7, 9, 67],
    [8, 10, 84],
  ])(
    "checks all exact coordinates for steps %s, strip %s, count %s",
    (steps, stripCount, count) => {
      const configuration = goebelStripConfiguration(
        `square-${count}-strip`,
        steps,
        stripCount,
        "2026-09-05",
      );
      expect(
        packingConfigurationSchema.safeParse(configuration).success,
      ).toBeTrue();
      expect(configuration.n).toBe(count);
      expect(configuration.squares).toHaveLength(count);
      expect(
        configuration.squares.filter(
          ({ orientation }) => orientation.angleRadiansApprox !== 0,
        ),
      ).toHaveLength(stripCount);
      expect(configuration.containerSide).toEqual({
        rational: { numerator: String(steps + 1), denominator: "1" },
        sqrtTwo: { numerator: "1", denominator: "2" },
        decimal: String(steps + 1 + Math.SQRT1_2),
      });
      expect(validateConfigurationGeometry(configuration)).toEqual([]);
    },
  );

  test("matches the staircase, corner and centered-strip formulas in Lean", () => {
    const configuration = goebelStripConfiguration(
      "square-27-strip",
      4,
      5,
      "2026-09-05",
    );
    expect(configuration.squares[0]!.center).toEqual({
      x: { numerator: "1", denominator: "2" },
      y: { numerator: "1", denominator: "2" },
    });
    expect(configuration.squares[4]!.center).toEqual({
      x: {
        rational: { numerator: "3", denominator: "2" },
        sqrtTwo: { numerator: "1", denominator: "2" },
      },
      y: {
        rational: { numerator: "9", denominator: "2" },
        sqrtTwo: { numerator: "1", denominator: "2" },
      },
    });
    expect(configuration.squares[20]!.center).toEqual({
      x: {
        rational: { numerator: "9", denominator: "2" },
        sqrtTwo: { numerator: "1", denominator: "2" },
      },
      y: { numerator: "1", denominator: "2" },
    });
    expect(configuration.squares[24]!.center).toEqual({
      x: {
        rational: { numerator: "5", denominator: "2" },
        sqrtTwo: { numerator: "1", denominator: "4" },
      },
      y: {
        rational: { numerator: "5", denominator: "2" },
        sqrtTwo: { numerator: "1", denominator: "4" },
      },
    });
  });

  test.each([
    [0, 1],
    [1.5, 1],
    [4, 0],
    [4, 2.5],
    [1, 2],
    [4, 6],
    [6, 9],
    [Number.MAX_SAFE_INTEGER, 1],
  ])(
    "rejects invalid dimensions or an overlong strip: %s, %s",
    (steps, stripCount) => {
      expect(() =>
        goebelStripConfiguration("invalid", steps, stripCount, "2026-09-05"),
      ).toThrow();
    },
  );
});

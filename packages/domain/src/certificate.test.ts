import { describe, expect, test } from "bun:test";
import { validateConfigurationGeometry } from "./certificate.ts";
import { goebelConfiguration, gridConfiguration } from "./configurations.ts";
import {
  compareExact,
  exactOne,
  exactZero,
  fromExact,
  multiplyExact,
  signExact,
} from "./exact.ts";
import { exactNumberSchema } from "./schema.ts";

const ratio = (numerator: string, denominator = "1") => ({
  numerator,
  denominator,
});
const surd = (rational: string, radical: string) =>
  fromExact({ rational: ratio(rational), sqrtTwo: ratio(radical) });

describe("exact quadratic arithmetic", () => {
  test("orders opposite-sign terms without floating-point rounding", () => {
    expect(signExact(surd("-1", "1"))).toBe(1);
    expect(signExact(surd("1", "-1"))).toBe(-1);
    expect(signExact(surd("-2", "1"))).toBe(-1);
    expect(signExact(surd("2", "-1"))).toBe(1);
    expect(signExact(surd("1", "1"))).toBe(1);
    expect(signExact(surd("-1", "-1"))).toBe(-1);
    expect(signExact(exactZero)).toBe(0);
    expect(signExact(surd("0", "-1"))).toBe(-1);
    expect(signExact(surd("0", "1"))).toBe(1);
    expect(signExact(surd("6369051672525773", "-4503599627370496"))).toBe(1);
    expect(signExact(surd("6369051672525772", "-4503599627370496"))).toBe(-1);
  });

  test("cancels conjugates exactly", () => {
    expect(
      compareExact(multiplyExact(surd("1", "1"), surd("-1", "1")), exactOne),
    ).toBe(0);
  });

  test("rejects zero denominators at the archive boundary", () => {
    expect(exactNumberSchema.safeParse(ratio("1", "0")).success).toBeFalse();
  });
});

describe("configuration certificates", () => {
  test.each([5, 10] as const)(
    "checks every containment and pair for Göbel's %s-square construction exactly",
    (count) => {
      const configuration = goebelConfiguration(
        `square-${count}-goebel`,
        count,
        "2026-09-05",
      );
      expect(configuration.squares).toHaveLength(count);
      expect(validateConfigurationGeometry(configuration)).toEqual([]);
      expect(configuration.certificate.method).toBe(
        "exact-quadratic-separating-axis",
      );
    },
  );

  test("rejects an overlapping square rather than trusting certificate metadata", () => {
    const configuration = gridConfiguration(
      "square-6-grid",
      6,
      3,
      "2026-09-05",
    );
    configuration.squares[1]!.center = configuration.squares[0]!.center;
    expect(validateConfigurationGeometry(configuration)).toContain(
      "Squares 0, 1: separation certificate failed",
    );
  });

  test("rejects a square outside its container", () => {
    const configuration = gridConfiguration(
      "square-1-grid",
      1,
      1,
      "2026-09-05",
    );
    configuration.squares[0]!.center.x = ratio("0");
    expect(validateConfigurationGeometry(configuration)).toContain(
      "Square 0: containment certificate failed",
    );
  });

  test("rejects a non-unit frame and a mismatched tangent", () => {
    const configuration = gridConfiguration(
      "square-1-grid",
      1,
      1,
      "2026-09-05",
    );
    configuration.squares[0]!.orientation.cosine = ratio("0");
    expect(validateConfigurationGeometry(configuration)).toContain(
      "Square 0: frame is not unit length",
    );
    expect(validateConfigurationGeometry(configuration)).toContain(
      "Square 0: tangent-half-angle does not match frame",
    );
  });

  test("rejects overstated margins", () => {
    const configuration = gridConfiguration(
      "square-6-grid",
      6,
      3,
      "2026-09-05",
    );
    configuration.certificate.minimumSeparationMargin = ratio("1");
    expect(
      validateConfigurationGeometry(configuration).some((error) =>
        error.includes("separation certificate failed"),
      ),
    ).toBeTrue();
  });
});

import { describe, expect, test } from "bun:test";
import {
  goebelConfiguration,
  gridConfiguration,
  type PackingConfiguration,
} from "@square-packing/domain";
import {
  certificateValue,
  renderQuadraticCertificate,
} from "./generate-quadratic-certificates.ts";

describe("quadratic Lean certificates", () => {
  test("emits exact coefficients and kernel checks for a quadratic packing", () => {
    const configuration = goebelConfiguration("square-5-test", 5, "2026-09-05");
    const output = renderQuadraticCertificate(configuration);
    expect(output).toContain(
      "namespace SquarePackingArchive.Records.Square5Test",
    );
    expect(output).toContain("QuadraticCertificate 2 5");
    expect(output).toContain("by decide +kernel");
    expect(output.match(/private theorem separated_row_/g)).toHaveLength(5);
    expect(output).toContain(
      "QuadraticCertificate.valid_of_rows boundaries_valid",
    );
    expect(output).toContain(
      "QuadraticCertificate.valid_sound certificate_valid",
    );
    expect(certificateValue(configuration)).toContain("Real.sqrt 2");
  });

  test("rejects overlapping coordinates before emitting a proof", () => {
    const configuration = gridConfiguration("overlapping", 2, 2, "2026-09-05");
    configuration.squares[1]!.center = configuration.squares[0]!.center;
    expect(() => renderQuadraticCertificate(configuration)).toThrow(
      "separation certificate failed",
    );
  });

  test("keeps sqrt(7) values exact", () => {
    const configuration: PackingConfiguration = gridConfiguration(
      "radical-side",
      1,
      1,
      "2026-09-05",
    );
    configuration.containerSide = {
      rational: { numerator: "13", denominator: "2" },
      radical: { numerator: "1", denominator: "2" },
      radicand: 7,
      decimal: "7.822875655532295",
    };
    expect(certificateValue(configuration)).toBe(
      "(((13 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7",
    );
    expect(renderQuadraticCertificate(configuration)).toContain(
      "QuadraticCertificate 7 1",
    );
  });

  test("rejects a count mismatch even when distinct ids match the declared count", () => {
    const configuration: PackingConfiguration = gridConfiguration(
      "wrong-count",
      3,
      3,
      "2026-09-05",
    );
    configuration.n = 2;
    configuration.squares[2]!.id = 1;
    expect(() => renderQuadraticCertificate(configuration)).toThrow(
      "Square ids must be distinct and match the square count",
    );
  });

  test("rejects mixed fields even when the geometry never combines the coordinates", () => {
    const configuration: PackingConfiguration = gridConfiguration(
      "mixed-centers",
      1,
      10,
      "2026-09-05",
    );
    const root = (radicand: number) => ({
      rational: { numerator: "0", denominator: "1" },
      radical: { numerator: "1", denominator: "1" },
      radicand,
    });
    configuration.squares[0]!.center = { x: root(2), y: root(7) };
    expect(() => renderQuadraticCertificate(configuration)).toThrow(
      "single quadratic field",
    );
  });
});

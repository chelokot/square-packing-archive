import { describe, expect, test } from "vitest";
import { archive } from "./archive.ts";
import { countFromSearch } from "./selection.ts";
import { angleGroup, squareAngle } from "./geometry.ts";
import { filterClaims } from "./components/ClaimsTable.tsx";

describe("explorer selection", () => {
  test("opens a shared n and rejects out-of-range or fractional parameters", () => {
    expect(countFromSearch("?n=11")).toBe(11);
    expect(countFromSearch("?n=100")).toBe(100);
    for (const search of [
      "",
      "?n=0",
      "?n=101",
      "?n=-1",
      "?n=8.5",
      "?n=8junk",
    ]) {
      expect(countFromSearch(search)).toBe(68);
    }
  });
});

describe("viewer geometry", () => {
  test("uses exact frame coordinates even when approximate metadata is stale", () => {
    const square = archive.configurationData[0]!.squares[0]!;
    const oriented = {
      ...square,
      orientation: {
        ...square.orientation,
        cosine: { numerator: "3", denominator: "5" },
        sine: { numerator: "4", denominator: "5" },
        angleRadiansApprox: 0,
      },
    };
    expect(squareAngle(oriented)).toBeCloseTo(53.1301023542, 8);
  });

  test("puts near-90 degree rotations in the same half-degree group as zero", () => {
    expect(angleGroup(89.99)).toBe(0);
    expect(angleGroup(0.01)).toBe(0);
    expect(angleGroup(44.8)).toBe(45);
  });
});

describe("catalog search", () => {
  test("searches exact n rather than matching n=11 when searching n=1", () => {
    const result = filterClaims(archive.claims, archive, "1", "all");
    expect(result.length).toBeGreaterThan(0);
    expect(result.every((claim) => claim.n === 1)).toBe(true);
  });

  test("combines author search and evidence filters", () => {
    const result = filterClaims(
      archive.claims,
      archive,
      "Friedman",
      "lean-verified",
    );
    expect(result.length).toBeGreaterThan(0);
    expect(
      result.every((claim) =>
        claim.contributors.some(({ author }) => author === "friedman"),
      ),
    ).toBe(true);
    expect(
      result.every((claim) =>
        claim.evidence.some((evidence) => evidence.kind === "lean-proof"),
      ),
    ).toBe(true);
    expect(
      filterClaims(archive.claims, archive, "no-such-author", "all"),
    ).toHaveLength(0);
  });
});

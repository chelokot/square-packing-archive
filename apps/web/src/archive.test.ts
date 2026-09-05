import { assert, describe, expect, test } from "vitest";
import { archive } from "./archive.ts";
import {
  explorerBoundFor,
  isGridBaseline,
  gridBaselineConfiguration,
  exactCoverageByYear,
  claimsByYear,
} from "@square-packing/domain";

describe("compiled archive", () => {
  test("distinguishes Brendberg's 2023 bound from Schadt's 2025 improvement", () => {
    expect(
      archive.claims.find(({ id }) => id === "upper-68-brendberg"),
    ).toMatchObject({
      announcedAt: "2023-06",
      value: { lean: "13 / 3 + 2 * Real.sqrt 5" },
    });
    expect(
      archive.claims.find(({ id }) => id === "upper-68-schadt"),
    ).toMatchObject({
      announcedAt: "2025-12-19",
      contributors: [
        { author: "brendberg", role: "discoverer" },
        { author: "schadt", role: "optimizer" },
      ],
      supersedes: "upper-68-brendberg",
    });
  });

  test("loads the exact 50-square record instead of an 8-by-8 grid", () => {
    const bound = explorerBoundFor(archive, 50)!;
    assert(!isGridBaseline(bound));
    expect(bound.value.lean).toBe("((53 : ℚ) / 7 : ℝ)");
    const configuration = archive.configurationData.find(
      ({ id }) => id === bound.configuration,
    )!;
    expect(configuration.containerSide).toEqual({
      numerator: "53",
      denominator: "7",
      decimal: "7.57142857142857",
    });
    expect(configuration.squares).toHaveLength(50);
    expect(
      configuration.squares.filter(
        ({ orientation }) =>
          "numerator" in orientation.tangentHalfAngle &&
          orientation.tangentHalfAngle.numerator === "1",
      ),
    ).toHaveLength(16);
  });

  test("all 100 explorer cells resolve without adding grid baselines to record history", () => {
    const withoutBaselines = { ...archive, gridBaseline: undefined };
    expect(exactCoverageByYear(archive)).toEqual(
      exactCoverageByYear(withoutBaselines),
    );
    expect(claimsByYear(archive)).toEqual(claimsByYear(withoutBaselines));
    for (let count = 1; count <= 100; count += 1) {
      const bound = explorerBoundFor(archive, count);
      expect(bound, `n = ${count}`).toBeDefined();
      if (isGridBaseline(bound!)) {
        expect(archive.claims.some((claim) => claim.n === count)).toBe(false);
        const configuration = gridBaselineConfiguration(bound!);
        expect(configuration.squares.length).toBe(count);
        expect(configuration.containerSide.decimal).toBe(bound!.value.decimal);
      }
    }
  });
  test("every catalogued square count has an explorable construction", () => {
    for (const count of new Set(archive.claims.map(({ n }) => n))) {
      expect(
        archive.configurationData.some(({ n }) => n === count),
        `n = ${count}`,
      ).toBe(true);
    }
  });
  test("loads every referenced configuration", () => {
    expect(archive.configurationData.map(({ id }) => id).sort()).toEqual(
      archive.configurations.map(({ id }) => id).sort(),
    );
  });

  test("every catalogued result has its own checked proof, including historical entries", () => {
    const publishedExact = archive.claims.filter(
      (claim) => claim.active && claim.relation === "exact",
    );
    const leanChecked = archive.claims.filter((claim) =>
      claim.evidence.some(
        (evidence) =>
          evidence.kind === "lean-proof" && evidence.status === "lean-checked",
      ),
    );
    expect(publishedExact.length).toBeGreaterThan(0);
    expect(leanChecked.length).toBe(archive.claims.length);
    expect(archive.claims.some(({ id }) => id === "upper-11-trump")).toBe(
      false,
    );
    expect(explorerBoundFor(archive, 11)?.value.decimal).toBe("3.88");
  });

  test("every active integer-side construction has coordinates at its stated bound", () => {
    for (const claim of archive.claims.filter(
      (claim) =>
        claim.active &&
        claim.relation !== "lower" &&
        /^\d+$/.test(claim.value.decimal),
    )) {
      const configuration = archive.configurationData.find(
        ({ id }) => id === claim.configuration,
      );
      expect(configuration, claim.id).toBeDefined();
      expect(configuration!.n).toBe(claim.n);
      expect(configuration!.containerSide.decimal).toBe(claim.value.decimal);
    }
  });
});

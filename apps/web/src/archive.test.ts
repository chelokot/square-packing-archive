import { describe, expect, test } from "vitest";
import { archive } from "./archive.ts";
import {
  explorerBoundFor,
  isGridBaseline,
  gridBaselineConfiguration,
  exactCoverageByYear,
  claimsByYear,
} from "@square-packing/domain";

describe("compiled archive", () => {
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

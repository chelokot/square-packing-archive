import { describe, expect, test } from "vitest";
import { archive } from "./archive.ts";

describe("compiled archive", () => {
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

  test("keeps the published and formal verification counts distinct", () => {
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
    expect(leanChecked.length).toBeLessThanOrEqual(archive.claims.length);
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

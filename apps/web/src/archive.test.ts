import { describe, expect, test } from "vitest";
import { archive } from "./archive.ts";

describe("compiled archive", () => {
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
});

import { describe, expect, test } from "bun:test";
import { manifestSchema } from "./schema.ts";
import {
  gridBaselineFor,
  gridBaselineConfiguration,
  explorerBoundFor,
} from "./baselines.ts";
import {
  activeClaims,
  claimsByYear,
  exactCoverageByYear,
  verificationLevel,
} from "./model.ts";
import { validateConfigurationGeometry } from "./certificate.ts";
import { validateArchiveReferences } from "./validate.ts";

const archive = manifestSchema.parse({
  schemaVersion: 1,
  updatedAt: "2026-09-05",
  problem: { symbol: "s", name: "Square packing", definition: "Test archive" },
  authors: [],
  sources: [
    {
      id: "archive-research",
      kind: "repository",
      title: "Proof library",
      authors: [],
      url: "https://example.com/proofs",
    },
  ],
  claims: [],
  configurations: [],
  gridBaseline: {
    through: 100,
    proof: {
      source: "archive-research",
      artifact: "formal/SquarePackingArchive/Records/GridBounds.lean",
      theorem: "SquarePackingArchive.Records.GridBounds.grid_hasPacking",
      checkedAt: "2026-09-05",
    },
  },
});

describe("derived grid bounds", () => {
  test("all supported counts have exact layouts at their checked bound", () => {
    for (let count = 1; count <= 100; count += 1) {
      const baseline = gridBaselineFor(archive, count)!;
      expect(baseline.side ** 2).toBeGreaterThanOrEqual(count);
      expect((baseline.side - 1) ** 2).toBeLessThan(count);
      expect(baseline.relation).toBe("upper");
      expect(verificationLevel(baseline)).toBe("lean-verified");
      expect(baseline.evidence[0]!.theorem).toBe(
        archive.gridBaseline!.proof.theorem,
      );
      const configuration = gridBaselineConfiguration(baseline);
      expect(configuration.n).toBe(count);
      expect(configuration.containerSide.decimal).toBe(baseline.value.decimal);
      expect(validateConfigurationGeometry(configuration)).toEqual([]);
      expect("announcedAt" in baseline).toBe(false);
    }
  });

  test("requires an explicit policy and respects its range", () => {
    expect(
      gridBaselineFor({ ...archive, gridBaseline: undefined }, 61),
    ).toBeUndefined();
    for (const count of [0, -1, 1.5, 101, NaN, Infinity]) {
      expect(gridBaselineFor(archive, count)).toBeUndefined();
    }
    const limited = {
      ...archive,
      gridBaseline: { ...archive.gridBaseline!, through: 60 },
    };
    expect(gridBaselineFor(limited, 60)).toBeDefined();
    expect(gridBaselineFor(limited, 61)).toBeUndefined();
  });

  test("does not replace a catalogued result or upgrade its evidence", () => {
    const claim = {
      id: "upper-61-record",
      n: 61,
      relation: "upper" as const,
      value: { decimal: "7.99" },
      announcedAt: "2020",
      contributors: [],
      active: true,
      evidence: [
        {
          kind: "tracker-record" as const,
          status: "reported" as const,
          source: "archive-research",
        },
      ],
    };
    expect(explorerBoundFor({ ...archive, claims: [claim] }, 61)).toBe(claim);
    expect(
      verificationLevel(explorerBoundFor({ ...archive, claims: [claim] }, 61)!),
    ).toBe("reported");
  });

  test("does not create historical events or exact-coverage milestones", () => {
    const original = JSON.stringify(archive);
    for (let count = 1; count <= 100; count += 1)
      explorerBoundFor(archive, count);
    expect(JSON.stringify(archive)).toBe(original);
    expect(activeClaims(archive)).toEqual([]);
    expect(claimsByYear(archive).size).toBe(0);
    expect(exactCoverageByYear(archive)).toEqual([]);
  });

  test("validates proof metadata and source references", () => {
    expect(validateArchiveReferences(archive, [])).toEqual([]);
    expect(
      validateArchiveReferences({ ...archive, sources: [] }, []),
    ).toContain("grid baseline: unknown source archive-research");
    const policy = archive.gridBaseline!;
    for (const proof of [
      { ...policy.proof, checkedAt: undefined },
      { ...policy.proof, artifact: "not-lean" },
      { ...policy.proof, theorem: "" },
    ]) {
      expect(
        manifestSchema.safeParse({
          ...archive,
          gridBaseline: { ...policy, proof },
        }).success,
      ).toBe(false);
    }
  });
});

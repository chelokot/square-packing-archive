import { describe, expect, test } from "bun:test";
import { claimSchema, evidenceSchema, manifestSchema } from "./schema.ts";
import type { Claim } from "./schema.ts";
import { exactCoverageByYear, isVerified, verificationLevel } from "./model.ts";

const claim = claimSchema.parse({
  id: "upper-1-example",
  n: 1,
  relation: "upper",
  value: { decimal: "1" },
  announcedAt: "2026",
  contributors: [],
  evidence: [
    {
      kind: "published-proof",
      status: "published",
      source: "example-source",
    },
  ],
  active: true,
});

const leanEvidence = evidenceSchema.parse({
  kind: "lean-proof",
  status: "lean-checked",
  source: "example-source",
  artifact: "formal/SquarePackingArchive/Example.lean",
  theorem: "SquarePackingArchive.Example",
  checkedAt: "2026-08-16",
});

const archiveWith = (claims: readonly Claim[]) =>
  manifestSchema.parse({
    schemaVersion: 1,
    updatedAt: "2026-09-04",
    problem: { symbol: "s", name: "Square packing", definition: "Example" },
    authors: [],
    sources: [],
    claims,
    configurations: [],
  });

describe("verificationLevel", () => {
  test("does not call a published paper verified", () => {
    expect(verificationLevel(claim)).toBe("published-unformalized");
    expect(isVerified(claim)).toBeFalse();
  });

  test("reserves verified status for Lean evidence", () => {
    const leanClaim = claimSchema.parse({
      ...claim,
      value: { decimal: "1", lean: "1" },
      evidence: [leanEvidence],
    });
    expect(verificationLevel(leanClaim)).toBe("lean-verified");
    expect(isVerified(leanClaim)).toBeTrue();
  });

  test("rejects Lean evidence without a formal target", () => {
    expect(() =>
      claimSchema.parse({
        ...claim,
        evidence: [leanEvidence],
      }),
    ).toThrow();
  });

  test("does not promote a reported proof to published evidence", () => {
    expect(
      verificationLevel({
        ...claim,
        evidence: [
          {
            kind: "published-proof",
            status: "reported",
            source: "example-source",
          },
        ],
      }),
    ).toBe("reported");
  });
});

describe("Lean verification dates", () => {
  test.each(["artifact", "theorem", "checkedAt"])(
    "requires %s on every new Lean evidence record",
    (field) => {
      const incomplete = { ...leanEvidence, [field]: undefined };
      expect(evidenceSchema.safeParse(incomplete).success).toBeFalse();
    },
  );

  test.each(["2026", "2026-08", "2026-02-30", "2026-13-01"])(
    "rejects incomplete or invalid calendar date %s",
    (checkedAt) => {
      expect(
        evidenceSchema.safeParse({ ...leanEvidence, checkedAt }).success,
      ).toBeFalse();
    },
  );

  test("reserves checkedAt for Lean evidence", () => {
    expect(
      evidenceSchema.safeParse({
        kind: "published-proof",
        status: "published",
        source: "example-source",
        checkedAt: "2026-08-16",
      }).success,
    ).toBeFalse();
  });
});

describe("exactCoverageByYear", () => {
  const historicalExact = claimSchema.parse({
    ...claim,
    id: "exact-1-historical",
    relation: "exact",
    value: { decimal: "1", lean: "1" },
    announcedAt: "1975",
    evidence: [...claim.evidence, leanEvidence],
  });

  test("counts a 1975 result as Lean verified only in 2026", () => {
    expect(exactCoverageByYear(archiveWith([historicalExact]))).toEqual([
      { year: 1975, published: 1, verified: 0 },
      { year: 2026, published: 1, verified: 1 },
    ]);
  });

  test("deduplicates n across proofs and preserves inactive historical results", () => {
    const archive = archiveWith([
      {
        ...historicalExact,
        id: "exact-1-later",
        announcedAt: "2005",
        evidence: [
          ...historicalExact.evidence,
          {
            ...leanEvidence,
            theorem: "SquarePackingArchive.Other",
            checkedAt: "2026-09-01",
          },
        ],
      },
      {
        ...historicalExact,
        active: false,
        evidence: [
          ...claim.evidence,
          { ...leanEvidence, checkedAt: "2025-12-31" },
        ],
      },
      {
        ...historicalExact,
        id: "exact-2-example",
        n: 2,
        announcedAt: "1979",
        evidence: claim.evidence,
      },
      {
        ...historicalExact,
        id: "upper-3-example",
        n: 3,
        relation: "upper",
        announcedAt: "1960",
      },
    ]);
    const original = structuredClone(archive);
    expect(exactCoverageByYear(archive)).toEqual([
      { year: 1975, published: 1, verified: 0 },
      { year: 1979, published: 2, verified: 0 },
      { year: 2005, published: 2, verified: 0 },
      { year: 2025, published: 2, verified: 1 },
      { year: 2026, published: 2, verified: 1 },
    ]);
    expect(archive).toEqual(original);
  });

  test("keeps Lean coverage independent from published coverage", () => {
    expect(
      exactCoverageByYear(
        archiveWith([{ ...historicalExact, evidence: [leanEvidence] }]),
      ),
    ).toEqual([{ year: 2026, published: 0, verified: 1 }]);
  });

  test("does not count tracker reports or unconfirmed proofs as published exact results", () => {
    expect(
      exactCoverageByYear(
        archiveWith([
          {
            ...historicalExact,
            evidence: [
              {
                kind: "tracker-record",
                status: "reported",
                source: "example-source",
              },
            ],
          },
          {
            ...historicalExact,
            id: "exact-2-reported",
            n: 2,
            evidence: [
              {
                kind: "published-proof",
                status: "reported",
                source: "example-source",
              },
            ],
          },
        ]),
      ),
    ).toEqual([]);
  });

  test("counts elementary published proofs and handles an empty archive", () => {
    expect(
      exactCoverageByYear(
        archiveWith([
          {
            ...historicalExact,
            evidence: [
              {
                kind: "elementary-proof",
                status: "published",
                source: "example-source",
              },
            ],
          },
        ]),
      ),
    ).toEqual([{ year: 1975, published: 1, verified: 0 }]);
    expect(exactCoverageByYear(archiveWith([]))).toEqual([]);
  });
});

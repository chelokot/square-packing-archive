import { describe, expect, test } from "bun:test";
import {
  claimSchema,
  compiledArchiveSchema,
  evidenceSchema,
  manifestSchema,
  type Claim,
} from "./schema.ts";
import { validateArchiveReferences } from "./validate.ts";

const publication = {
  kind: "published-proof" as const,
  status: "published" as const,
  source: "example-source",
};

const leanProof = evidenceSchema.parse({
  kind: "lean-proof",
  status: "lean-checked",
  source: "example-source",
  artifact: "formal/SquarePackingArchive/Records/Basic.lean",
  theorem: "SquarePackingArchive.Records.Basic.s1_eq_one",
  checkedAt: "2026-09-05",
});

const historicalClaim = claimSchema.parse({
  id: "exact-1-historical",
  n: 1,
  relation: "exact",
  value: { decimal: "1", lean: "1" },
  announcedAt: "1975",
  contributors: [],
  evidence: [publication],
  active: false,
});

const checkedClaim: Claim = {
  ...historicalClaim,
  evidence: [publication, leanProof],
};

const archiveWith = (claims: readonly Claim[]) =>
  manifestSchema.parse({
    schemaVersion: 1,
    updatedAt: "2026-09-05",
    problem: { symbol: "s", name: "Square packing", definition: "Test" },
    authors: [],
    sources: [
      {
        id: "example-source",
        kind: "publication",
        title: "Original proof",
        authors: [],
        url: "https://example.com/proof",
      },
    ],
    claims,
    configurations: [],
  });

const compiledWith = (claims: readonly Claim[]) => ({
  ...archiveWith([]),
  claims,
  configurationData: [],
});

describe("Lean-only catalog publication", () => {
  test.each([true, false])(
    "rejects an unformalized claim with active=%s",
    (active) => {
      const claim = { ...historicalClaim, active };
      const archive = archiveWith([claim]);
      expect(validateArchiveReferences(archive, [])).toContain(
        `${claim.id}: Catalog claims require a Lean proof; keep unformalized proposals in issues`,
      );
      const parsed = compiledArchiveSchema.safeParse(compiledWith([claim]));
      expect(parsed.success).toBeFalse();
      if (!parsed.success) {
        expect(parsed.error.issues[0]!.path).toEqual(["claims", 0, "evidence"]);
      }
    },
  );

  test("preserves published provenance on an inactive formalized result", () => {
    const archive = archiveWith([checkedClaim]);
    expect(validateArchiveReferences(archive, [])).toEqual([]);
    const compiled = compiledArchiveSchema.parse(compiledWith([checkedClaim]));
    expect(compiled.claims[0]).toEqual(checkedClaim);
  });

  test("requires each claim's own proof rather than another proof for the same n", () => {
    const claims = [
      {
        ...checkedClaim,
        id: "upper-1-checked",
        relation: "upper" as const,
        active: true,
      },
      historicalClaim,
    ];
    expect(validateArchiveReferences(archiveWith(claims), [])).toHaveLength(1);
    expect(
      compiledArchiveSchema.safeParse(compiledWith(claims)).success,
    ).toBeFalse();
  });

  test("keeps general schemas usable for unformalized historical analysis", () => {
    expect(claimSchema.safeParse(historicalClaim).success).toBeTrue();
    expect(
      manifestSchema.safeParse(archiveWith([historicalClaim])).success,
    ).toBeTrue();
  });

  test.each(["artifact", "theorem", "checkedAt"] as const)(
    "rejects a Lean label without %s at both publication boundaries",
    (field) => {
      const malformed: Claim = {
        ...checkedClaim,
        evidence: [{ ...leanProof, [field]: undefined }],
      };
      expect(
        validateArchiveReferences(
          { ...archiveWith([]), claims: [malformed] },
          [],
        ),
      ).toContain(`${malformed.id}: Lean evidence requires ${field}`);
      expect(
        compiledArchiveSchema.safeParse(compiledWith([malformed])).success,
      ).toBeFalse();
    },
  );

  test("rejects malformed proof references, dates, statuses and missing target expressions", () => {
    const malformedClaims: Claim[] = [
      {
        ...checkedClaim,
        evidence: [{ ...leanProof, artifact: "https://example.com/claim" }],
      },
      {
        ...checkedClaim,
        evidence: [{ ...leanProof, theorem: "trust this label" }],
      },
      {
        ...checkedClaim,
        evidence: [{ ...leanProof, checkedAt: "2026-02-30" }],
      },
      { ...checkedClaim, evidence: [{ ...leanProof, status: "published" }] },
      {
        ...checkedClaim,
        evidence: [{ ...publication, status: "lean-checked" }],
      },
      { ...checkedClaim, value: { decimal: "1" } },
    ];
    for (const claim of malformedClaims) {
      expect(
        validateArchiveReferences({ ...archiveWith([]), claims: [claim] }, [])
          .length,
      ).toBeGreaterThan(0);
      expect(
        compiledArchiveSchema.safeParse(compiledWith([claim])).success,
      ).toBeFalse();
    }
  });
});

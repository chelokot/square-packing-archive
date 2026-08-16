import { describe, expect, test } from "bun:test";
import { claimSchema } from "./schema.ts";
import { isVerified, verificationLevel } from "./model.ts";

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

describe("verificationLevel", () => {
  test("does not call a published paper verified", () => {
    expect(verificationLevel(claim)).toBe("published-unformalized");
    expect(isVerified(claim)).toBeFalse();
  });

  test("reserves verified status for Lean evidence", () => {
    const leanClaim = claimSchema.parse({
      ...claim,
      evidence: [
        {
          kind: "lean-proof",
          status: "lean-checked",
          source: "example-source",
          theorem: "SquarePackingArchive.Example",
        },
      ],
    });
    expect(verificationLevel(leanClaim)).toBe("lean-verified");
    expect(isVerified(leanClaim)).toBeTrue();
  });
});

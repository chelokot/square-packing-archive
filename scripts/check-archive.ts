import { loadArchive } from "./archive.ts";

const archive = await loadArchive();
const verifiedClaims = archive.claims.filter((claim) =>
  claim.evidence.some(
    (evidence) =>
      evidence.kind === "lean-proof" && evidence.status === "lean-checked",
  ),
);
console.log(
  `Archive valid: ${archive.claims.length} claims, ${archive.configurationData.length} configurations, ${verifiedClaims.length} Lean-verified claims`,
);

import { loadArchive } from "./archive.ts";
import { readmeCoveragePath, renderReadmeCoverage } from "./readme-coverage.ts";

const archive = await loadArchive();
if (
  (await Bun.file(readmeCoveragePath).text()) !== renderReadmeCoverage(archive)
) {
  throw new Error("README coverage is stale; run bun run archive:build");
}
const verifiedClaims = archive.claims.filter((claim) =>
  claim.evidence.some(
    (evidence) =>
      evidence.kind === "lean-proof" && evidence.status === "lean-checked",
  ),
);
console.log(
  `Archive valid: ${archive.claims.length} claims, ${archive.configurationData.length} configurations, ${verifiedClaims.length} Lean-verified claims`,
);

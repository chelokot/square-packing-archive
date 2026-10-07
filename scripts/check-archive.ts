import { isFormalProof } from "@square-packing/domain";
import { loadArchive } from "./archive.ts";
import { readmeCoveragePath, renderReadmeCoverage } from "./readme-coverage.ts";

const archive = await loadArchive();
if (
  (await Bun.file(readmeCoveragePath).text()) !== renderReadmeCoverage(archive)
) {
  throw new Error("README coverage is stale; run bun run archive:build");
}
const verifiedClaims = archive.claims.filter((claim) =>
  claim.evidence.some(isFormalProof),
);
console.log(
  `Archive valid: ${archive.claims.length} claims, ${archive.configurationData.length} configurations, ${verifiedClaims.length} formally verified claims`,
);

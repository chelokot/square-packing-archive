import { loadArchive, archiveRoot } from "./archive.ts";
import { readmeCoveragePath, renderReadmeCoverage } from "./readme-coverage.ts";

const archive = await loadArchive();
const destination = new URL("apps/web/src/generated/archive.json", archiveRoot);
await Bun.write(destination, `${JSON.stringify(archive)}\n`);
await Bun.write(readmeCoveragePath, renderReadmeCoverage(archive));
console.log(
  `Built ${archive.claims.length} claims and ${archive.configurationData.length} configurations`,
);

import { loadArchive, archiveRoot } from "./archive.ts";

const archive = await loadArchive();
const destination = new URL("apps/web/src/generated/archive.json", archiveRoot);
await Bun.write(destination, `${JSON.stringify(archive)}\n`);
console.log(
  `Built ${archive.claims.length} claims and ${archive.configurationData.length} configurations`,
);

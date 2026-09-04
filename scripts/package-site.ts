import { cp, mkdir, mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { resolve } from "node:path";
import { $ } from "bun";

const root = resolve(import.meta.dir, "..");
const builtSite = resolve(root, "apps/web/dist");
const hosting: { project_id: string } = JSON.parse(
  await readFile(resolve(root, ".openai/hosting.json"), "utf8"),
);
await readFile(resolve(builtSite, "index.html"));
const staging = await mkdtemp(resolve(tmpdir(), "square-packing-site-"));
const artifact = resolve(root, "dist/site.tar.gz");

try {
  const deployment = resolve(staging, "dist");
  await mkdir(resolve(deployment, ".openai"), { recursive: true });
  await cp(builtSite, resolve(deployment, "client"), { recursive: true });
  await Bun.write(
    resolve(deployment, ".openai/hosting.json"),
    JSON.stringify({ ...hosting, static: { directory: "dist/client" } }),
  );
  await mkdir(resolve(root, "dist"), { recursive: true });
  await $`tar -C ${staging} -czf ${artifact} dist`;
  console.log(artifact);
} finally {
  await rm(staging, { recursive: true });
}

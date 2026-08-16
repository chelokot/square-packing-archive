import {
  manifestSchema,
  packingConfigurationSchema,
  validateArchiveReferences,
  type CompiledArchive,
} from "@square-packing/domain";

const root = new URL("../", import.meta.url);
const manifestPath = new URL("archive/manifest.json", root);

export const loadArchive = async (): Promise<CompiledArchive> => {
  const manifest = manifestSchema.parse(await Bun.file(manifestPath).json());
  const configurationData = await Promise.all(
    manifest.configurations.map(async (reference) =>
      packingConfigurationSchema.parse(
        await Bun.file(new URL(`archive/${reference.path}`, root)).json(),
      ),
    ),
  );
  const errors = validateArchiveReferences(manifest, configurationData);
  if (errors.length > 0) {
    throw new Error(errors.join("\n"));
  }
  return { ...manifest, configurationData };
};

export const archiveRoot = root;

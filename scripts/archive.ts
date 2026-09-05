import {
  manifestSchema,
  packingConfigurationSchema,
  validateArchiveReferences,
  type CompiledArchive,
  gridConfiguration,
  goebelConfiguration,
  goebelStripConfiguration,
  validateConfigurationGeometry,
} from "@square-packing/domain";

const root = new URL("../", import.meta.url);
const manifestPath = new URL("archive/manifest.json", root);

export const loadArchive = async (): Promise<CompiledArchive> => {
  const manifest = manifestSchema.parse(await Bun.file(manifestPath).json());
  const configurationData = await Promise.all(
    manifest.configurations.map(async (reference) => {
      if ("path" in reference) {
        return packingConfigurationSchema.parse(
          await Bun.file(new URL(`archive/${reference.path}`, root)).json(),
        );
      }
      switch (reference.recipe) {
        case "grid":
          return gridConfiguration(
            reference.id,
            reference.n,
            reference.side,
            manifest.updatedAt,
          );
        case "goebel":
          return goebelConfiguration(
            reference.id,
            reference.n,
            manifest.updatedAt,
          );
        case "goebel-strip":
          return goebelStripConfiguration(
            reference.id,
            reference.steps,
            reference.stripCount,
            manifest.updatedAt,
          );
      }
    }),
  );
  const errors = [
    ...validateArchiveReferences(manifest, configurationData),
    ...configurationData.flatMap((configuration) =>
      validateConfigurationGeometry(configuration).map(
        (error) => `${configuration.id}: ${error}`,
      ),
    ),
  ];
  if (errors.length > 0) {
    throw new Error(errors.join("\n"));
  }
  return { ...manifest, configurationData };
};

export const archiveRoot = root;

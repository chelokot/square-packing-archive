import type { ArchiveManifest, PackingConfiguration } from "./schema.ts";

const duplicates = (values: readonly string[]): readonly string[] => {
  const counts = Map.groupBy(values, (value) => value);
  return [...counts.entries()]
    .filter(([, occurrences]) => occurrences.length > 1)
    .map(([value]) => value);
};

export const validateArchiveReferences = (
  manifest: ArchiveManifest,
  configurations: readonly PackingConfiguration[],
): readonly string[] => {
  const errors: string[] = [];
  const authorIds = new Set(manifest.authors.map((author) => author.id));
  const sourceIds = new Set(manifest.sources.map((source) => source.id));
  const claimIds = new Set(manifest.claims.map((claim) => claim.id));
  const configurationIds = new Set(
    configurations.map((configuration) => configuration.id),
  );

  for (const [label, values] of [
    ["author", manifest.authors.map((author) => author.id)],
    ["source", manifest.sources.map((source) => source.id)],
    ["claim", manifest.claims.map((claim) => claim.id)],
    ["configuration", configurations.map((configuration) => configuration.id)],
  ] as const) {
    for (const duplicate of duplicates(values)) {
      errors.push(`duplicate ${label} id: ${duplicate}`);
    }
  }

  for (const source of manifest.sources) {
    for (const author of source.authors) {
      if (!authorIds.has(author)) {
        errors.push(`${source.id}: unknown author ${author}`);
      }
    }
  }

  for (const claim of manifest.claims) {
    for (const contributor of claim.contributors) {
      if (!authorIds.has(contributor.author)) {
        errors.push(`${claim.id}: unknown contributor ${contributor.author}`);
      }
    }
    for (const evidence of claim.evidence) {
      if (!sourceIds.has(evidence.source)) {
        errors.push(`${claim.id}: unknown source ${evidence.source}`);
      }
      if (
        evidence.status === "lean-checked" &&
        evidence.kind !== "lean-proof"
      ) {
        errors.push(`${claim.id}: only Lean evidence can be lean-checked`);
      }
      if (
        evidence.kind === "lean-proof" &&
        evidence.status !== "lean-checked"
      ) {
        errors.push(`${claim.id}: Lean evidence must be lean-checked`);
      }
    }
    if (claim.supersedes !== undefined && !claimIds.has(claim.supersedes)) {
      errors.push(`${claim.id}: unknown superseded claim ${claim.supersedes}`);
    }
    if (
      claim.configuration !== undefined &&
      !configurationIds.has(claim.configuration)
    ) {
      errors.push(`${claim.id}: unknown configuration ${claim.configuration}`);
    }
  }

  for (const configuration of configurations) {
    if (configuration.squares.length !== configuration.n) {
      errors.push(
        `${configuration.id}: expected ${configuration.n} squares, got ${configuration.squares.length}`,
      );
    }
    const claim = manifest.claims.find(
      (candidate) => candidate.configuration === configuration.id,
    );
    if (claim === undefined) {
      errors.push(
        `${configuration.id}: configuration is not referenced by a claim`,
      );
    } else if (claim.value.decimal !== configuration.containerSide.decimal) {
      errors.push(
        `${configuration.id}: claim and configuration side lengths differ`,
      );
    }
  }

  return errors;
};

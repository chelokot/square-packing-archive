import type { ArchiveManifest, PackingConfiguration } from "./schema.ts";
import { catalogClaimSchema } from "./schema.ts";

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
  if (
    manifest.gridBaseline !== undefined &&
    !sourceIds.has(manifest.gridBaseline.proof.source)
  ) {
    errors.push(
      `grid baseline: unknown source ${manifest.gridBaseline.proof.source}`,
    );
  }
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
    const catalogClaim = catalogClaimSchema.safeParse(claim);
    if (!catalogClaim.success) {
      for (const issue of catalogClaim.error.issues) {
        errors.push(`${claim.id}: ${issue.message}`);
      }
    }
    for (const contributor of claim.contributors) {
      if (!authorIds.has(contributor.author)) {
        errors.push(`${claim.id}: unknown contributor ${contributor.author}`);
      }
    }
    for (const evidence of claim.evidence) {
      if (!sourceIds.has(evidence.source)) {
        errors.push(`${claim.id}: unknown source ${evidence.source}`);
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
    const configuration = configurations.find(
      ({ id }) => id === claim.configuration,
    );
    if (configuration !== undefined) {
      if (claim.n !== configuration.n)
        errors.push(
          `${claim.id}: claim and configuration square counts differ`,
        );
      if (claim.value.decimal !== configuration.containerSide.decimal)
        errors.push(`${claim.id}: claim and configuration side lengths differ`);
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
    }
  }

  return errors;
};

import type {
  ArchiveManifest,
  Claim,
  CompiledArchive,
  Evidence,
  PackingConfiguration,
  Ratio,
} from "./schema.ts";

export type VerificationLevel =
  | "computational-evidence"
  | "lean-verified"
  | "published-unformalized"
  | "reported";

const evidenceLevel = (evidence: Evidence): VerificationLevel => {
  if (evidence.kind === "lean-proof" && evidence.status === "lean-checked") {
    return "lean-verified";
  }
  if (
    evidence.kind === "published-proof" ||
    evidence.kind === "elementary-proof"
  ) {
    return "published-unformalized";
  }
  if (
    evidence.kind === "interval-certificate" ||
    evidence.kind === "elementary-construction"
  ) {
    return "computational-evidence";
  }
  return "reported";
};

const verificationPriority: Readonly<Record<VerificationLevel, number>> = {
  reported: 0,
  "computational-evidence": 1,
  "published-unformalized": 2,
  "lean-verified": 3,
};

export const verificationLevel = (claim: Claim): VerificationLevel =>
  claim.evidence
    .map(evidenceLevel)
    .reduce((strongest, current) =>
      verificationPriority[current] > verificationPriority[strongest]
        ? current
        : strongest,
    );

export const isVerified = (claim: Claim): boolean =>
  verificationLevel(claim) === "lean-verified";

export const ratioToNumber = (ratio: Ratio): number =>
  Number(ratio.numerator) / Number(ratio.denominator);

export const activeClaims = (archive: ArchiveManifest): readonly Claim[] =>
  archive.claims.filter((claim) => claim.active);

export const currentClaimFor = (
  archive: ArchiveManifest,
  squareCount: number,
): Claim | undefined =>
  archive.claims.find((claim) => claim.active && claim.n === squareCount);

export const configurationFor = (
  archive: CompiledArchive,
  configurationId: string,
): PackingConfiguration | undefined =>
  archive.configurationData.find(
    (configuration) => configuration.id === configurationId,
  );

export const claimsByYear = (
  archive: ArchiveManifest,
): ReadonlyMap<number, readonly Claim[]> => {
  const grouped = Map.groupBy(archive.claims, (claim) =>
    Number(claim.announcedAt.slice(0, 4)),
  );
  return new Map(
    [...grouped.entries()].sort(
      ([leftYear], [rightYear]) => leftYear - rightYear,
    ),
  );
};

export const exactCoverageByYear = (
  archive: ArchiveManifest,
): readonly { year: number; published: number; verified: number }[] => {
  const exactClaims = archive.claims
    .filter((claim) => claim.relation === "exact")
    .sort((left, right) => left.announcedAt.localeCompare(right.announcedAt));
  const years = [
    ...new Set(
      exactClaims.map((claim) => Number(claim.announcedAt.slice(0, 4))),
    ),
  ];
  return years.map((year) => {
    const known = exactClaims.filter(
      (claim) => Number(claim.announcedAt.slice(0, 4)) <= year,
    );
    return {
      year,
      published: new Set(known.map((claim) => claim.n)).size,
      verified: new Set(known.filter(isVerified).map((claim) => claim.n)).size,
    };
  });
};

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

const isPublishedProof = (evidence: Evidence): boolean =>
  evidence.status === "published" &&
  (evidence.kind === "published-proof" || evidence.kind === "elementary-proof");

const evidenceLevel = (evidence: Evidence): VerificationLevel => {
  if (evidence.kind === "lean-proof" && evidence.status === "lean-checked") {
    return "lean-verified";
  }
  if (isPublishedProof(evidence)) {
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
  const exactClaims = archive.claims.filter(
    (claim) => claim.relation === "exact",
  );
  const published = exactClaims
    .filter((claim) => claim.evidence.some(isPublishedProof))
    .map((claim) => ({
      n: claim.n,
      year: Number(claim.announcedAt.slice(0, 4)),
    }));
  const verified = exactClaims.flatMap((claim) =>
    claim.evidence.flatMap((evidence) =>
      evidence.kind === "lean-proof" &&
      evidence.status === "lean-checked" &&
      evidence.checkedAt !== undefined
        ? [{ n: claim.n, year: Number(evidence.checkedAt.slice(0, 4)) }]
        : [],
    ),
  );
  const years = [
    ...new Set([...published, ...verified].map(({ year }) => year)),
  ].sort((left, right) => left - right);
  const countThrough = (events: typeof published, year: number): number =>
    new Set(
      events.filter((event) => event.year <= year).map((event) => event.n),
    ).size;
  return years.map((year) => ({
    year,
    published: countThrough(published, year),
    verified: countThrough(verified, year),
  }));
};

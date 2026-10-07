import {
  bendLawNames,
  isFormalProof,
  isGridBaseline,
  type Claim,
  type CompiledArchive,
  type FormalProof,
  type ExplorerBound,
} from "@square-packing/domain";
import { copy, repositoryUrl } from "../copy.ts";

export const claimRelationSymbols = {
  exact: "=",
  upper: "≤",
  lower: "≥",
} as const satisfies Record<Claim["relation"], string>;

export const claimValue = (
  claim: Pick<Claim, "n" | "relation" | "value">,
): string =>
  `s(${claim.n}) ${claimRelationSymbols[claim.relation]} ${claim.value.expression ?? claim.value.decimal}`;

export const explorerBoundDescription = (bound: ExplorerBound): string =>
  `${copy.claimRelations[bound.relation]} · ${claimValue(bound)}${isGridBaseline(bound) ? ` · ${copy.gridBaseline}` : ""}`;

export const proofTitle = (
  bound: ExplorerBound,
  evidence: FormalProof,
): string =>
  evidence.kind === "bend-proof" && !isGridBaseline(bound)
    ? bendLawNames(bound).join(", ")
    : evidence.theorem!;

export const contributorNames = (
  archive: CompiledArchive,
  claim: Claim,
): string =>
  claim.contributors.length === 0
    ? copy.elementary
    : claim.contributors
        .map(
          ({ author }) => archive.authors.find(({ id }) => id === author)!.name,
        )
        .join(", ");

export const ClaimLinks = ({
  archive,
  claim,
}: {
  archive: CompiledArchive;
  claim: Claim;
}) => {
  const sources = [
    ...new Set(
      claim.evidence
        .filter((evidence) => !isFormalProof(evidence))
        .map((evidence) => evidence.source),
    ),
  ];
  const proofs = claim.evidence.filter(isFormalProof);
  return (
    <div className="flex flex-wrap gap-x-3 gap-y-2 text-xs text-forest">
      {sources.map((id) => {
        const source = archive.sources.find((item) => item.id === id)!;
        return (
          <a
            key={id}
            href={source.url}
            title={source.title}
            className="underline decoration-forest/30 underline-offset-4"
          >
            {copy.source}
          </a>
        );
      })}
      {proofs.map((evidence) => (
        <a
          key={proofTitle(claim, evidence)}
          href={`${repositoryUrl}/blob/main/${evidence.artifact}`}
          title={proofTitle(claim, evidence)}
          className="underline decoration-forest/30 underline-offset-4"
        >
          {copy.proof[evidence.kind]}
        </a>
      ))}
    </div>
  );
};

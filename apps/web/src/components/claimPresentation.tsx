import {
  isGridBaseline,
  verificationLevel,
  type Claim,
  type CompiledArchive,
  type ExplorerBound,
} from "@square-packing/domain";
import { copy, repositoryUrl } from "../copy.ts";
import { evidencePresentation } from "./EvidenceBadge.tsx";

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
  `${copy.claimRelations[bound.relation]} · ${evidencePresentation[verificationLevel(bound)].label} · ${claimValue(bound)}${isGridBaseline(bound) ? ` · ${copy.gridBaseline}` : ""}`;

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
        .filter((evidence) => evidence.kind !== "lean-proof")
        .map((evidence) => evidence.source),
    ),
  ];
  const proofs = claim.evidence.filter(
    (evidence) => evidence.kind === "lean-proof",
  );
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
          key={evidence.theorem}
          href={`${repositoryUrl}/blob/main/${evidence.artifact}`}
          title={evidence.theorem}
          className="underline decoration-forest/30 underline-offset-4"
        >
          {copy.proof}
        </a>
      ))}
    </div>
  );
};

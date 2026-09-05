import type { CompiledArchive } from "@square-packing/domain";
import { copy } from "../copy.ts";
import { BoundHistory } from "./BoundHistory.tsx";
import {
  ClaimLinks,
  claimValue,
  contributorNames,
} from "./claimPresentation.tsx";

export const RecordTimeline = ({
  archive,
  squareCount,
}: {
  archive: CompiledArchive;
  squareCount: number;
}) => {
  const claims = archive.claims
    .filter((claim) => claim.n === squareCount)
    .sort((left, right) => right.announcedAt.localeCompare(left.announcedAt));
  return (
    <div>
      <h3 className="font-serif text-2xl">{copy.historyTitle(squareCount)}</h3>
      <BoundHistory claims={claims} />
      {claims.length === 0 ? (
        <p className="mt-5 border-y border-rule py-8 text-sm text-muted">
          {copy.noHistory}
        </p>
      ) : (
        <ol className="mt-5 divide-y divide-rule border-y border-rule">
          {claims.map((claim) => (
            <li
              key={claim.id}
              className="grid gap-3 py-5 sm:grid-cols-[4rem_minmax(0,1fr)]"
            >
              <div className="font-mono text-xs text-muted">
                {claim.announcedAt.slice(0, 4)}
              </div>
              <div>
                <div className="flex flex-wrap items-center justify-between gap-2">
                  <p className="font-mono text-sm">{claimValue(claim)}</p>
                </div>
                <p className="mb-3 mt-2 text-xs leading-5 text-muted">
                  {contributorNames(archive, claim)}
                  <span className="mx-2">·</span>
                  {claim.active ? copy.current : copy.historical}
                </p>
                <ClaimLinks archive={archive} claim={claim} />
              </div>
            </li>
          ))}
        </ol>
      )}
    </div>
  );
};

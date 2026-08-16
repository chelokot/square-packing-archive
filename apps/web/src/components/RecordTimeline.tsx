import type { Claim, CompiledArchive } from "@square-packing/domain";
import { ArrowDownRight } from "lucide-react";
import { EvidenceBadge } from "./EvidenceBadge.tsx";

const year = (claim: Claim): number => Number(claim.announcedAt.slice(0, 4));

export const RecordTimeline = ({
  archive,
  squareCount,
}: {
  archive: CompiledArchive;
  squareCount: number;
}) => {
  const claims = archive.claims
    .filter((claim) => claim.n === squareCount)
    .sort((left, right) => left.announcedAt.localeCompare(right.announcedAt));
  const authorById = new Map(
    archive.authors.map((author) => [author.id, author]),
  );

  if (claims.length === 0) {
    return (
      <div className="flex min-h-56 items-center justify-center rounded-3xl border border-dashed border-white/10 bg-white/[0.02] p-8 text-center text-sm text-slate-500">
        No curated record for n={squareCount} yet. The import queue remains
        explicit rather than silently guessing.
      </div>
    );
  }

  return (
    <div className="overflow-hidden rounded-3xl border border-white/10 bg-ink-900/70">
      <div className="border-b border-white/10 px-5 py-5 md:px-7">
        <p className="font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
          Record lineage
        </p>
        <h2 className="mt-2 text-2xl font-semibold text-white">
          s({squareCount})
        </h2>
      </div>
      <ol className="divide-y divide-white/[0.07]">
        {claims.map((claim, index) => (
          <li
            key={claim.id}
            className="grid gap-4 px-5 py-5 sm:grid-cols-[5rem_1fr_auto] sm:items-center md:px-7"
          >
            <div className="font-mono text-sm text-slate-500">
              {year(claim)}
            </div>
            <div>
              <div className="flex items-baseline gap-2">
                <span className="font-mono text-lg text-white">
                  {claim.relation === "upper"
                    ? "≤"
                    : claim.relation === "lower"
                      ? "≥"
                      : "="}{" "}
                  {claim.value.decimal}
                </span>
                {index > 0 && claim.relation === "upper" ? (
                  <ArrowDownRight className="size-4 text-mint-300" />
                ) : null}
              </div>
              <p className="mt-1 text-sm text-slate-400">
                {claim.contributors.length === 0
                  ? "Elementary construction"
                  : claim.contributors
                      .map(
                        ({ author }) => authorById.get(author)?.name ?? author,
                      )
                      .join(", ")}
              </p>
            </div>
            <EvidenceBadge claim={claim} />
          </li>
        ))}
      </ol>
    </div>
  );
};

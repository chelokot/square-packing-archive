import { activeClaims, type CompiledArchive } from "@square-packing/domain";
import { ExternalLink, FileCode2 } from "lucide-react";
import { EvidenceBadge } from "./EvidenceBadge.tsx";

export const ClaimsTable = ({ archive }: { archive: CompiledArchive }) => {
  const authors = new Map(archive.authors.map((author) => [author.id, author]));
  const sources = new Map(archive.sources.map((source) => [source.id, source]));
  const claims = [...activeClaims(archive)].sort(
    (left, right) => left.n - right.n,
  );

  return (
    <section
      id="claims"
      className="overflow-hidden rounded-3xl border border-white/10 bg-ink-900/70"
    >
      <div className="border-b border-white/10 px-5 py-6 md:px-7">
        <p className="font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
          Canonical claims
        </p>
        <h2 className="mt-2 text-2xl font-semibold tracking-tight text-white">
          Current curated bounds
        </h2>
        <p className="mt-2 max-w-2xl text-sm leading-6 text-slate-400">
          A paper is evidence and a Lean theorem is verification. They remain
          visibly distinct.
        </p>
      </div>
      <div className="overflow-x-auto">
        <table className="w-full min-w-[52rem] border-collapse text-left text-sm">
          <thead className="bg-white/[0.025] font-mono text-[0.68rem] uppercase tracking-[0.16em] text-slate-500">
            <tr>
              <th className="px-6 py-4 font-medium">n</th>
              <th className="px-6 py-4 font-medium">Claim</th>
              <th className="px-6 py-4 font-medium">Year</th>
              <th className="px-6 py-4 font-medium">Contributors</th>
              <th className="px-6 py-4 font-medium">Status</th>
              <th className="px-6 py-4 font-medium">Artifacts</th>
            </tr>
          </thead>
          <tbody className="divide-y divide-white/[0.06]">
            {claims.map((claim) => {
              const source = sources.get(claim.evidence[0]!.source);
              const leanEvidence = claim.evidence.find(
                (evidence) => evidence.kind === "lean-proof",
              );
              return (
                <tr
                  key={claim.id}
                  className="transition hover:bg-white/[0.025]"
                >
                  <td className="px-6 py-4 font-mono text-white">{claim.n}</td>
                  <td className="px-6 py-4">
                    <span className="font-mono text-slate-200">
                      s({claim.n}){" "}
                      {claim.relation === "exact"
                        ? "="
                        : claim.relation === "upper"
                          ? "≤"
                          : "≥"}{" "}
                      {claim.value.expression ?? claim.value.decimal}
                    </span>
                  </td>
                  <td className="px-6 py-4 font-mono text-slate-500">
                    {claim.announcedAt.slice(0, 4)}
                  </td>
                  <td className="px-6 py-4 text-slate-400">
                    {claim.contributors.length === 0
                      ? "Elementary"
                      : claim.contributors
                          .map(
                            ({ author }) => authors.get(author)?.name ?? author,
                          )
                          .join(", ")}
                  </td>
                  <td className="px-6 py-4">
                    <EvidenceBadge claim={claim} />
                  </td>
                  <td className="px-6 py-4">
                    <div className="flex items-center gap-2">
                      {source === undefined ? null : (
                        <a
                          href={source.url}
                          target="_blank"
                          rel="noreferrer"
                          title={source.title}
                          className="grid size-8 place-items-center rounded-lg border border-white/10 text-slate-400 transition hover:border-cyan-300/40 hover:text-cyan-300"
                        >
                          <ExternalLink
                            className="size-3.5"
                            aria-hidden="true"
                          />
                        </a>
                      )}
                      {leanEvidence?.theorem === undefined ||
                      leanEvidence.artifact === undefined ? null : (
                        <a
                          href={`https://github.com/chelokot/square-packing-archive/blob/main/${leanEvidence.artifact}`}
                          target="_blank"
                          rel="noreferrer"
                          title={leanEvidence.theorem}
                          className="grid size-8 place-items-center rounded-lg border border-mint-300/30 text-mint-300"
                        >
                          <FileCode2 className="size-3.5" aria-hidden="true" />
                        </a>
                      )}
                    </div>
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
      </div>
    </section>
  );
};

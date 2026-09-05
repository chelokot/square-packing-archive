import {
  activeClaims,
  type CompiledArchive,
  type Claim,
} from "@square-packing/domain";
import { Search } from "lucide-react";
import { useState } from "react";
import { copy } from "../copy.ts";
import {
  ClaimLinks,
  claimValue,
  contributorNames,
} from "./claimPresentation.tsx";

export const filterClaims = (
  claims: readonly Claim[],
  archive: CompiledArchive,
  query: string,
): readonly Claim[] => {
  const search = query.trim().toLocaleLowerCase();
  return claims.filter((claim) => {
    const matchesText = /^\d+$/.test(search)
      ? claim.n === Number(search) ||
        (search.length === 4 && claim.announcedAt.startsWith(search))
      : [
          String(claim.n),
          claim.announcedAt,
          claimValue(claim),
          contributorNames(archive, claim),
        ]
          .join(" ")
          .toLocaleLowerCase()
          .includes(search);
    return matchesText;
  });
};

export const ClaimsTable = ({
  archive,
  onSelect,
}: {
  archive: CompiledArchive;
  onSelect: (count: number) => void;
}) => {
  const [query, setQuery] = useState("");
  const claims = [...activeClaims(archive)].sort(
    (left, right) => left.n - right.n,
  );
  const filtered = filterClaims(claims, archive, query);
  return (
    <section id="claims" className="scroll-mt-6 border-t border-rule py-8">
      <h2 className="flex items-center gap-3 text-lg font-semibold">
        {copy.catalogTitle}
      </h2>
      <p className="mt-3 text-sm leading-6 text-muted">
        {copy.catalogDescription}
      </p>
      <div className="my-5 flex flex-wrap items-center gap-3">
        <label className="flex min-w-0 flex-1 items-center gap-2 border border-rule bg-surface px-3 sm:max-w-sm">
          <Search className="size-4 shrink-0 text-muted" aria-hidden="true" />
          <input
            type="search"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            placeholder={copy.search}
            aria-label={copy.search}
            className="min-w-0 flex-1 bg-transparent py-2.5 text-sm"
          />
        </label>
        <span role="status" className="text-xs text-muted sm:ml-auto">
          {copy.resultCount(filtered.length, claims.length)}
        </span>
      </div>
      <div className="overflow-x-auto border-y border-rule">
        <table className="w-full min-w-[48rem] border-collapse text-left text-sm">
          <thead className="bg-paper text-xs text-muted">
            <tr>
              {Object.values(copy.columns).map((column) => (
                <th
                  scope="col"
                  key={column}
                  className="px-4 py-3 font-medium first:pl-0 last:pr-0"
                >
                  {column}
                </th>
              ))}
            </tr>
          </thead>
          <tbody className="divide-y divide-rule">
            {filtered.map((claim) => (
              <tr key={claim.id} className="hover:bg-surface">
                <th scope="row" className="py-4 pr-4 font-mono font-normal">
                  <a
                    href="#explore"
                    onClick={() => onSelect(claim.n)}
                    className="text-forest underline decoration-forest/30 underline-offset-4"
                  >
                    {claim.n}
                  </a>
                </th>
                <td className="px-4 py-4 font-mono text-xs">
                  {claimValue(claim)}
                </td>
                <td className="px-4 py-4 font-mono text-xs text-muted">
                  {claim.announcedAt.slice(0, 4)}
                </td>
                <td className="px-4 py-4 text-xs text-muted">
                  {contributorNames(archive, claim)}
                </td>
                <td className="py-4 pl-4">
                  <ClaimLinks archive={archive} claim={claim} />
                </td>
              </tr>
            ))}
          </tbody>
        </table>
        {filtered.length === 0 ? (
          <p className="py-10 text-center text-sm text-muted">
            {copy.noMatches}
          </p>
        ) : null}
      </div>
    </section>
  );
};

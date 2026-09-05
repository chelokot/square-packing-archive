import {
  activeClaims,
  explorerBoundFor,
  type CompiledArchive,
} from "@square-packing/domain";
import { copy } from "../copy.ts";
import { explorerBoundDescription } from "./claimPresentation.tsx";
import {
  coveragePresentation,
  coveragePresentationFor,
} from "./coveragePresentation.ts";

export const CoverageMatrix = ({
  archive,
  selectedCount,
  onSelect,
}: {
  archive: CompiledArchive;
  selectedCount: number;
  onSelect: (count: number) => void;
}) => {
  const exactCount = new Set(
    activeClaims(archive)
      .filter((claim) => claim.relation === "exact")
      .map(({ n }) => n),
  ).size;
  return (
    <section
      id="matrix"
      aria-label={copy.matrixTitle}
      className="w-full min-w-0 max-w-[21rem]"
    >
      <p className="text-xs text-muted">
        <span className="font-mono text-forest">{exactCount}</span>{" "}
        {copy.exactCount}
      </p>
      <div className="@container mt-4 grid grid-cols-10 gap-1">
        {Array.from({ length: 100 }, (_, index) => index + 1).map((count) => {
          const claim = explorerBoundFor(archive, count);
          const presentation = coveragePresentationFor(claim);
          const description =
            claim === undefined
              ? copy.emptyStatus
              : explorerBoundDescription(claim);
          const label = copy.matrixCellLabel(count, description);
          return (
            <button
              key={count}
              type="button"
              aria-label={label}
              aria-pressed={count === selectedCount}
              onClick={() => onSelect(count)}
              className={`group relative aspect-square border font-mono text-[0.65rem] hover:z-20 hover:border-ink focus-visible:z-20 ${presentation.className} ${count === selectedCount ? "outline outline-2 outline-offset-1 outline-ink z-10 font-bold" : ""}`}
            >
              <span>{count}</span>
              <span
                aria-hidden="true"
                className={`pointer-events-none absolute bottom-full z-30 mb-2 w-max max-w-[min(16rem,50cqw)] border border-rule bg-surface px-2 py-1.5 text-left font-sans text-xs leading-5 font-normal text-ink opacity-0 shadow-sm group-hover:opacity-100 group-focus-visible:opacity-100 ${(count - 1) % 10 < 5 ? "left-0" : "right-0"}`}
              >
                {label}
              </span>
            </button>
          );
        })}
      </div>
      <div className="mt-4 flex flex-wrap gap-x-5 gap-y-2 text-[0.65rem] text-muted">
        {Object.values(coveragePresentation).map(({ label, className }) => (
          <span key={label} className="flex items-center gap-2">
            <i aria-hidden="true" className={`size-2.5 border ${className}`} />
            {label}
          </span>
        ))}
      </div>
    </section>
  );
};

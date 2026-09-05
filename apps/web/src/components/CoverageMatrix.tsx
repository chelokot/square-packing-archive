import {
  strongestClaimFor,
  exactToNumber,
  verificationLevel,
  type CompiledArchive,
} from "@square-packing/domain";
import { ChevronLeft, ChevronRight } from "lucide-react";
import { copy } from "../copy.ts";
import { evidencePresentation } from "./EvidenceBadge.tsx";
import { claimRelationSymbols, claimValue } from "./claimPresentation.tsx";

export const CoverageMatrix = ({
  archive,
  selectedCount,
  onSelect,
}: {
  archive: CompiledArchive;
  selectedCount: number;
  onSelect: (count: number) => void;
}) => {
  return (
    <section id="matrix">
      <h3 className="text-sm font-medium">{copy.matrixTitle}</h3>
      <div className="my-4 flex items-center justify-between border border-rule bg-surface">
        <button
          type="button"
          disabled={selectedCount === 1}
          onClick={() => onSelect(selectedCount - 1)}
          aria-label={copy.previous}
          className="p-3 hover:bg-paper"
        >
          <ChevronLeft className="size-4" />
        </button>
        <label className="flex items-center gap-2 font-mono text-lg">
          n =
          <select
            aria-label={copy.squareCount}
            value={selectedCount}
            onChange={(event) => onSelect(Number(event.target.value))}
            className="bg-transparent py-2 pr-2"
          >
            {Array.from({ length: 100 }, (_, index) => (
              <option key={index} value={index + 1}>
                {index + 1}
              </option>
            ))}
          </select>
        </label>
        <button
          type="button"
          disabled={selectedCount === 100}
          onClick={() => onSelect(selectedCount + 1)}
          aria-label={copy.next}
          className="p-3 hover:bg-paper"
        >
          <ChevronRight className="size-4" />
        </button>
      </div>
      <div className="@container grid grid-cols-10 gap-1">
        {Array.from({ length: 100 }, (_, index) => index + 1).map((count) => {
          const claim = strongestClaimFor(archive, count);
          const presentation =
            claim === undefined
              ? {
                  label: copy.emptyStatus,
                  className: "border-rule/70 text-muted bg-surface",
                }
              : evidencePresentation[verificationLevel(claim)];
          const description =
            claim === undefined
              ? presentation.label
              : `${copy.claimRelations[claim.relation]} · ${presentation.label} · ${claimValue(claim)}`;
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
              {claim !== undefined && (
                <span
                  aria-hidden="true"
                  className={`absolute right-0.5 bottom-0.5 text-[0.6rem] leading-none ${claim.relation === "upper" ? "text-bound" : ""}`}
                >
                  {claimRelationSymbols[claim.relation]}
                </span>
              )}
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
      <div className="mt-4 flex flex-wrap gap-x-3 gap-y-1 text-[0.65rem] text-muted">
        {Object.entries(claimRelationSymbols).map(([relation, symbol]) => (
          <span key={relation} className="flex items-center gap-1.5">
            <span
              className={`font-mono text-xs ${relation === "upper" ? "text-bound" : ""}`}
              aria-hidden="true"
            >
              {symbol}
            </span>
            {copy.claimRelations[relation as keyof typeof claimRelationSymbols]}
          </span>
        ))}
      </div>
      <div className="mt-4 grid grid-cols-2 gap-x-3 gap-y-2 text-[0.65rem] text-muted">
        {[
          [copy.matrixVerified, "bg-forest-soft border-forest/40"],
          [copy.matrixPublished, "bg-ochre-soft border-ochre/40"],
          [copy.matrixComputed, "bg-plum-soft border-plum/40"],
          [copy.matrixReported, "bg-paper border-rule"],
        ].map(([label, color]) => (
          <span key={label} className="flex items-center gap-2">
            <i className={`size-2.5 border ${color}`} />
            {label}
          </span>
        ))}
      </div>
      <div className="mt-6 border-t border-rule pt-4">
        <p className="mb-3 text-xs text-muted">{copy.rotatedLayouts}</p>
        <div className="flex flex-wrap gap-2">
          {archive.configurationData
            .filter((configuration) =>
              configuration.squares.some(
                (square) =>
                  exactToNumber(square.orientation.sine) !== 0 &&
                  exactToNumber(square.orientation.cosine) !== 0,
              ),
            )
            .map((configuration) => (
              <button
                key={configuration.id}
                type="button"
                onClick={() => onSelect(configuration.n)}
                aria-pressed={configuration.n === selectedCount}
                className={`border px-3 py-1.5 font-mono text-xs ${configuration.n === selectedCount ? "border-forest bg-forest text-surface" : "border-rule hover:border-forest"}`}
              >
                n = {configuration.n}
              </button>
            ))}
        </div>
        <p className="mt-3 text-[0.65rem] leading-5 text-muted">
          {copy.gridLayouts}
        </p>
      </div>
    </section>
  );
};

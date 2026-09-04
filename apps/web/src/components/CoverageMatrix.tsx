import {
  activeClaims,
  verificationLevel,
  type CompiledArchive,
} from "@square-packing/domain";
import { ChevronLeft, ChevronRight } from "lucide-react";
import { copy } from "../copy.ts";
import { evidencePresentation } from "./EvidenceBadge.tsx";

export const CoverageMatrix = ({
  archive,
  selectedCount,
  onSelect,
}: {
  archive: CompiledArchive;
  selectedCount: number;
  onSelect: (count: number) => void;
}) => {
  const claims = activeClaims(archive);
  const ranks = {
    reported: 0,
    "computational-evidence": 1,
    "published-unformalized": 2,
    "lean-verified": 3,
  };
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
      <div className="grid grid-cols-10 gap-1">
        {Array.from({ length: 100 }, (_, index) => index + 1).map((count) => {
          const claim = claims
            .filter((item) => item.n === count)
            .sort(
              (left, right) =>
                ranks[verificationLevel(right)] -
                ranks[verificationLevel(left)],
            )[0];
          const presentation =
            claim === undefined
              ? {
                  label: copy.emptyStatus,
                  className: "border-rule/70 text-muted bg-surface",
                }
              : evidencePresentation[verificationLevel(claim)];
          return (
            <button
              key={count}
              type="button"
              aria-label={`n = ${count}: ${presentation.label}`}
              title={`n = ${count}: ${presentation.label}`}
              aria-pressed={count === selectedCount}
              onClick={() => onSelect(count)}
              className={`aspect-square border font-mono text-[0.65rem] hover:border-ink ${presentation.className} ${count === selectedCount ? "outline outline-2 outline-offset-1 outline-ink z-10 font-bold" : ""}`}
            >
              {count}
            </button>
          );
        })}
      </div>
      <p className="mt-4 text-xs leading-5 text-muted">{copy.matrixHelp}</p>
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
        <p className="mb-3 text-xs text-muted">{copy.availableLayouts}</p>
        <div className="flex flex-wrap gap-2">
          {archive.configurationData.map((configuration) => (
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
      </div>
    </section>
  );
};

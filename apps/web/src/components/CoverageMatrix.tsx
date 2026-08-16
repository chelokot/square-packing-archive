import {
  currentClaimFor,
  isVerified,
  verificationLevel,
  type CompiledArchive,
} from "@square-packing/domain";

const cellStyle = (archive: CompiledArchive, squareCount: number): string => {
  const claim = currentClaimFor(archive, squareCount);
  if (claim === undefined) {
    return "border-white/5 bg-white/[0.025] text-slate-600 hover:border-white/20 hover:text-slate-300";
  }
  if (isVerified(claim)) {
    return "border-mint-300/45 bg-mint-300/15 text-mint-300 shadow-[0_0_1rem_rgba(98,245,200,0.08)]";
  }
  if (claim.relation === "exact") {
    return "border-amber-300/35 bg-amber-300/10 text-amber-300";
  }
  if (verificationLevel(claim) === "computational-evidence") {
    return "border-violet-300/35 bg-violet-300/10 text-violet-300";
  }
  return "border-cyan-300/20 bg-cyan-300/[0.06] text-cyan-300";
};

export const CoverageMatrix = ({
  archive,
  selectedCount,
  onSelect,
}: {
  archive: CompiledArchive;
  selectedCount: number;
  onSelect: (squareCount: number) => void;
}) => (
  <section
    id="matrix"
    className="rounded-3xl border border-white/10 bg-ink-900/70 p-5 shadow-2xl shadow-black/20 backdrop-blur md:p-7"
  >
    <div className="mb-6 flex flex-col justify-between gap-4 sm:flex-row sm:items-end">
      <div>
        <p className="mb-2 font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
          Proof matrix · n ≤ 100
        </p>
        <h2 className="text-2xl font-semibold tracking-tight text-white">
          Every status, without ambiguity
        </h2>
      </div>
      <div className="flex flex-wrap gap-x-4 gap-y-2 text-xs text-slate-400">
        <span>
          <i className="mr-1.5 inline-block size-2 rounded-full bg-mint-300" />
          Lean verified
        </span>
        <span>
          <i className="mr-1.5 inline-block size-2 rounded-full bg-amber-300" />
          Published exact
        </span>
        <span>
          <i className="mr-1.5 inline-block size-2 rounded-full bg-violet-300" />
          Computed
        </span>
        <span>
          <i className="mr-1.5 inline-block size-2 rounded-full bg-cyan-300" />
          Reported
        </span>
      </div>
    </div>
    <div className="grid grid-cols-10 gap-1.5 sm:gap-2">
      {Array.from({ length: 100 }, (_, index) => index + 1).map(
        (squareCount) => (
          <button
            key={squareCount}
            type="button"
            onClick={() => onSelect(squareCount)}
            aria-pressed={selectedCount === squareCount}
            className={`aspect-square rounded-lg border font-mono text-[0.62rem] transition sm:rounded-xl sm:text-xs ${cellStyle(archive, squareCount)} ${selectedCount === squareCount ? "ring-2 ring-white/80 ring-offset-2 ring-offset-ink-900" : ""}`}
          >
            {squareCount}
          </button>
        ),
      )}
    </div>
  </section>
);

import {
  exactCoverageByYear,
  type CompiledArchive,
} from "@square-packing/domain";

const chartWidth = 720;
const chartHeight = 240;
const padding = 34;

const points = (
  values: readonly { year: number; count: number }[],
  maximum: number,
): string => {
  const minimumYear = Math.min(...values.map(({ year }) => year));
  const maximumYear = Math.max(...values.map(({ year }) => year));
  return values
    .map(({ year, count }) => {
      const x =
        padding +
        ((year - minimumYear) / Math.max(1, maximumYear - minimumYear)) *
          (chartWidth - padding * 2);
      const y =
        chartHeight -
        padding -
        (count / Math.max(1, maximum)) * (chartHeight - padding * 2);
      return `${x},${y}`;
    })
    .join(" ");
};

export const CoverageChart = ({ archive }: { archive: CompiledArchive }) => {
  const coverage = exactCoverageByYear(archive);
  const maximum = Math.max(...coverage.map(({ published }) => published));
  const published = coverage.map(({ year, published: count }) => ({
    year,
    count,
  }));
  const verified = coverage.map(({ year, verified: count }) => ({
    year,
    count,
  }));
  const firstYear = coverage.at(0)?.year ?? 1975;
  const lastYear = coverage.at(-1)?.year ?? 2026;

  return (
    <section className="rounded-3xl border border-white/10 bg-ink-900/70 p-5 md:p-7">
      <p className="mb-2 font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
        Formalization gap
      </p>
      <div className="mb-5 flex items-end justify-between gap-4">
        <div>
          <h2 className="text-2xl font-semibold tracking-tight text-white">
            Exact results over time
          </h2>
          <p className="mt-2 max-w-xl text-sm leading-6 text-slate-400">
            Amber records what the literature proves. Mint only moves when Lean
            accepts the theorem.
          </p>
        </div>
        <div className="hidden text-right font-mono text-xs text-slate-500 sm:block">
          {firstYear} → {lastYear}
        </div>
      </div>
      <svg
        viewBox={`0 0 ${chartWidth} ${chartHeight}`}
        className="w-full overflow-visible"
        role="img"
        aria-label="Published and Lean-verified exact results by year"
      >
        {[0, 0.25, 0.5, 0.75, 1].map((fraction) => {
          const y =
            chartHeight - padding - fraction * (chartHeight - padding * 2);
          return (
            <g key={fraction}>
              <line
                x1={padding}
                x2={chartWidth - padding}
                y1={y}
                y2={y}
                stroke="rgba(255,255,255,.07)"
              />
              <text
                x={padding - 10}
                y={y + 4}
                textAnchor="end"
                fill="#64748b"
                fontSize="10"
              >
                {Math.round(maximum * fraction)}
              </text>
            </g>
          );
        })}
        <polyline
          points={points(published, maximum)}
          fill="none"
          stroke="#ffc66d"
          strokeWidth="3"
          strokeLinejoin="round"
        />
        <polyline
          points={points(verified, maximum)}
          fill="none"
          stroke="#62f5c8"
          strokeWidth="3"
          strokeLinejoin="round"
        />
        <circle
          cx={chartWidth - padding}
          cy={chartHeight - padding}
          r="5"
          fill="#62f5c8"
        />
      </svg>
      <div className="mt-2 flex gap-5 text-xs text-slate-400">
        <span>
          <i className="mr-2 inline-block h-0.5 w-5 align-middle bg-amber-300" />
          Published exact
        </span>
        <span>
          <i className="mr-2 inline-block h-0.5 w-5 align-middle bg-mint-300" />
          Lean verified
        </span>
      </div>
    </section>
  );
};

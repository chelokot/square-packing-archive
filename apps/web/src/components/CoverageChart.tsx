import {
  exactCoverageByYear,
  type CompiledArchive,
} from "@square-packing/domain";
import { copy } from "../copy.ts";

export const CoverageChart = ({ archive }: { archive: CompiledArchive }) => {
  const coverage = exactCoverageByYear(archive);
  if (coverage.length === 0) return null;
  const firstYear = coverage[0]!.year;
  const lastYear = coverage[coverage.length - 1]!.year;
  const maximum = Math.max(
    1,
    ...coverage.flatMap(({ published, verified }) => [published, verified]),
  );
  const horizontal = (year: number) =>
    38 + ((year - firstYear) / Math.max(1, lastYear - firstYear)) * 528;
  const vertical = (count: number) => 198 - (count / maximum) * 170;
  const path = (key: "published" | "verified") =>
    coverage
      .map((point, index) =>
        index === 0
          ? `M ${horizontal(point.year)} ${vertical(point[key])}`
          : `H ${horizontal(point.year)} V ${vertical(point[key])}`,
      )
      .join(" ");
  const latest = coverage[coverage.length - 1]!;
  return (
    <div>
      <h3 className="font-serif text-2xl">{copy.coverageTitle}</h3>
      <p className="mt-3 max-w-xl text-xs leading-6 text-muted">
        {copy.coverageDescription}
      </p>
      <svg
        viewBox="0 0 600 235"
        className="mt-4 w-full"
        role="img"
        aria-label={copy.coverageTitle}
      >
        {[0, Math.round(maximum / 2), maximum].map((value) => (
          <g key={value}>
            <line
              x1="38"
              x2="566"
              y1={vertical(value)}
              y2={vertical(value)}
              stroke="var(--color-rule)"
            />
            <text
              x="28"
              y={vertical(value) + 4}
              textAnchor="end"
              fontSize="11"
              fill="var(--color-muted)"
            >
              {value}
            </text>
          </g>
        ))}
        <path
          d={path("published")}
          fill="none"
          stroke="var(--color-ochre)"
          strokeWidth="2"
        />
        <path
          d={path("verified")}
          fill="none"
          stroke="var(--color-forest)"
          strokeWidth="2"
        />
        <circle
          cx={horizontal(lastYear)}
          cy={vertical(latest.published)}
          r="3"
          fill="var(--color-ochre)"
        />
        <circle
          cx={horizontal(lastYear)}
          cy={vertical(latest.verified)}
          r="3"
          fill="var(--color-forest)"
        />
        <text x="38" y="224" fontSize="11" fill="var(--color-muted)">
          {firstYear}
        </text>
        <text
          x="566"
          y="224"
          textAnchor="end"
          fontSize="11"
          fill="var(--color-muted)"
        >
          {lastYear}
        </text>
      </svg>
      <div className="flex flex-wrap gap-x-5 gap-y-2 text-xs">
        <span className="text-ochre">
          {copy.coveragePublished}{" "}
          <b className="ml-1 font-mono">{latest.published}</b>
        </span>
        <span className="text-forest">
          {copy.coverageVerified}{" "}
          <b className="ml-1 font-mono">{latest.verified}</b>
        </span>
      </div>
      <details className="mt-5 text-xs text-muted">
        <summary className="py-2">{copy.coverageData}</summary>
        <table className="mt-2 w-full text-left">
          <thead>
            <tr>
              <th scope="col" className="py-2">
                {copy.columns.date}
              </th>
              <th scope="col">{copy.coveragePublished}</th>
              <th scope="col">{copy.coverageVerified}</th>
            </tr>
          </thead>
          <tbody>
            {coverage.map((point) => (
              <tr key={point.year} className="border-t border-rule font-mono">
                <th scope="row" className="py-2 font-normal">
                  {point.year}
                </th>
                <td>{point.published}</td>
                <td>{point.verified}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </details>
    </div>
  );
};

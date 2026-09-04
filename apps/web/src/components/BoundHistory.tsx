import type { Claim } from "@square-packing/domain";
import { copy } from "../copy.ts";

export const improvingUpperBounds = (
  claims: readonly Claim[],
): readonly Claim[] => {
  const ordered = claims
    .filter((claim) => claim.relation !== "lower")
    .toSorted((left, right) =>
      left.announcedAt.localeCompare(right.announcedAt),
    );
  return ordered.reduce<Claim[]>((records, claim) => {
    const previous = records.at(-1);
    if (
      previous === undefined ||
      Number(claim.value.decimal) < Number(previous.value.decimal)
    )
      records.push(claim);
    return records;
  }, []);
};

export const BoundHistory = ({ claims }: { claims: readonly Claim[] }) => {
  const records = improvingUpperBounds(claims);
  if (records.length < 2) return null;
  const initial = records[0]!;
  const latest = records[records.length - 1]!;
  const maximum = Number(initial.value.decimal);
  const minimum = Number(latest.value.decimal);
  const firstYear = Number(initial.announcedAt.slice(0, 4));
  const lastYear = Number(latest.announcedAt.slice(0, 4));
  const horizontal = (claim: Claim) =>
    74 +
    ((Number(claim.announcedAt.slice(0, 4)) - firstYear) /
      Math.max(1, lastYear - firstYear)) *
      414;
  const vertical = (claim: Claim) =>
    25 + ((maximum - Number(claim.value.decimal)) / (maximum - minimum)) * 100;
  const path = records
    .map((claim, index) =>
      index === 0
        ? `M ${horizontal(claim)} ${vertical(claim)}`
        : `H ${horizontal(claim)} V ${vertical(claim)}`,
    )
    .join(" ");
  return (
    <figure className="mt-5 border border-rule bg-surface px-3 pt-4">
      <figcaption className="px-2 text-xs text-muted">
        {copy.boundHistory}
      </figcaption>
      <svg
        viewBox="0 0 560 155"
        className="w-full"
        role="img"
        aria-label={copy.boundHistory}
      >
        {[initial, latest].map((claim) => (
          <g key={claim.id}>
            <line
              x1="74"
              x2="488"
              y1={vertical(claim)}
              y2={vertical(claim)}
              stroke="var(--color-rule)"
            />
            <text
              x="66"
              y={vertical(claim) + 4}
              textAnchor="end"
              fontSize="10"
              fill="var(--color-muted)"
            >
              {Number(claim.value.decimal).toFixed(5)}
            </text>
          </g>
        ))}
        <path
          d={path}
          fill="none"
          stroke="var(--color-ink)"
          strokeWidth="1.5"
        />
        {records.map((claim) => (
          <circle
            key={claim.id}
            cx={horizontal(claim)}
            cy={vertical(claim)}
            r="3"
            fill="var(--color-ink)"
          >
            <title>
              {claim.announcedAt}: ≤ {claim.value.decimal}
            </title>
          </circle>
        ))}
        <text x="74" y="147" fontSize="10" fill="var(--color-muted)">
          {firstYear}
        </text>
        {lastYear !== firstYear ? (
          <text
            x="488"
            y="147"
            textAnchor="end"
            fontSize="10"
            fill="var(--color-muted)"
          >
            {lastYear}
          </text>
        ) : null}
      </svg>
    </figure>
  );
};

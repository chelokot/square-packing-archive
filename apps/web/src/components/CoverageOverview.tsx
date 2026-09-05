import {
  explorerBoundFor,
  verificationLevel,
  type ArchiveManifest,
  type VerificationLevel,
} from "@square-packing/domain";
import { copy } from "../copy.ts";
import {
  claimRelationSymbols,
  explorerBoundDescription,
} from "./claimPresentation.tsx";

const colors = {
  "lean-verified": { fill: "#e1e9dc", ink: "#315d40" },
  "published-unformalized": { fill: "#f3e8d4", ink: "#835c23" },
  "computational-evidence": { fill: "#eee6f1", ink: "#6e5879" },
  reported: { fill: "#f5f3ec", ink: "#686c62" },
} satisfies Record<VerificationLevel, { fill: string; ink: string }>;

const emptyColors = { fill: "#fffef9", ink: "#686c62" };
const upperBoundInk = "#a13f35";

export const CoverageOverview = ({ archive }: { archive: ArchiveManifest }) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    viewBox="0 0 840 328"
    width="840"
    height="328"
    role="img"
    aria-labelledby="coverage-title coverage-description"
  >
    <title id="coverage-title">{copy.coverageOverviewTitle}</title>
    <desc id="coverage-description">{copy.coverageOverviewDescription}</desc>
    <rect width="840" height="328" rx="4" fill="#f5f3ec" />
    <g fontFamily="Arial, sans-serif" fill="#686c62">
      <text x="22" y="29" fontSize="17" fontWeight="600" fill="#252b27">
        {copy.coverageOverviewTitle}
      </text>
      <text x="818" y="28" textAnchor="end" fontSize="11">
        {archive.updatedAt}
      </text>
      <text x="22" y="48" fontSize="11">
        {copy.coverageOverviewScope}
      </text>
      {Array.from({ length: 100 }, (_, index) => {
        const count = index + 1;
        const claim = explorerBoundFor(archive, count);
        const palette =
          claim === undefined ? emptyColors : colors[verificationLevel(claim)];
        const label =
          claim === undefined
            ? copy.emptyStatus
            : explorerBoundDescription(claim);
        return (
          <g
            key={count}
            data-n={count}
            transform={`translate(${22 + (index % 20) * 40}, ${63 + Math.floor(index / 20) * 40})`}
            fontFamily="Consolas, monospace"
          >
            <title>{copy.matrixCellLabel(count, label)}</title>
            <rect
              width="35"
              height="35"
              fill={palette.fill}
              stroke={claim === undefined ? "#d8d9ce" : palette.ink}
              strokeOpacity={claim === undefined ? 1 : 0.35}
            />
            <text
              x="17.5"
              y="21"
              textAnchor="middle"
              fontSize="12"
              fill={palette.ink}
            >
              {count}
            </text>
            {claim !== undefined && (
              <text
                x="31"
                y="31"
                textAnchor="end"
                fontSize="10"
                fill={claim.relation === "upper" ? upperBoundInk : palette.ink}
              >
                {claimRelationSymbols[claim.relation]}
              </text>
            )}
          </g>
        );
      })}
      {Object.entries(claimRelationSymbols).map(([relation, symbol], index) => (
        <g key={relation} transform={`translate(${22 + index * 130}, 282)`}>
          <text
            fontFamily="Consolas, monospace"
            fontSize="14"
            fill={relation === "upper" ? upperBoundInk : undefined}
          >
            {symbol}
          </text>
          <text x="18" fontSize="11">
            {copy.claimRelations[relation as keyof typeof claimRelationSymbols]}
          </text>
        </g>
      ))}
      {(
        [
          [copy.matrixVerified, colors["lean-verified"]],
          [copy.matrixPublished, colors["published-unformalized"]],
          [copy.matrixComputed, colors["computational-evidence"]],
          [copy.matrixReported, colors.reported],
          [copy.emptyStatus, emptyColors],
        ] as const
      ).map(([label, palette], index) => (
        <g key={label} transform={`translate(${22 + index * 160}, 305)`}>
          <rect
            y="-9"
            width="10"
            height="10"
            fill={palette.fill}
            stroke={palette.ink}
            strokeOpacity="0.35"
          />
          <text x="18" fontSize="11">
            {label}
          </text>
        </g>
      ))}
    </g>
  </svg>
);

import { explorerBoundFor, type ArchiveManifest } from "@square-packing/domain";
import { copy } from "../copy.ts";
import { explorerBoundDescription } from "./claimPresentation.tsx";

import {
  coveragePresentation,
  coveragePresentationFor,
} from "./coveragePresentation.ts";

export const CoverageOverview = ({ archive }: { archive: ArchiveManifest }) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    viewBox="0 0 840 304"
    width="840"
    height="304"
    role="img"
    aria-labelledby="coverage-title coverage-description"
  >
    <title id="coverage-title">{copy.coverageOverviewTitle}</title>
    <desc id="coverage-description">{copy.coverageOverviewDescription}</desc>
    <rect width="840" height="304" rx="4" fill="#f5f3ec" />
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
        const palette = coveragePresentationFor(claim);
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
          </g>
        );
      })}
      {Object.values(coveragePresentation).map((palette, index) => (
        <g
          key={palette.label}
          transform={`translate(${22 + index * 160}, 283)`}
        >
          <rect
            y="-9"
            width="10"
            height="10"
            fill={palette.fill}
            stroke={palette.ink}
            strokeOpacity="0.35"
          />
          <text x="18" fontSize="11">
            {palette.label}
          </text>
        </g>
      ))}
    </g>
  </svg>
);

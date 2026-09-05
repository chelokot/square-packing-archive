import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";
import type { ArchiveManifest } from "@square-packing/domain";
import { CoverageOverview } from "../apps/web/src/components/CoverageOverview.tsx";
import { archiveRoot } from "./archive.ts";

export const readmeCoveragePath = new URL(
  "docs/assets/coverage.svg",
  archiveRoot,
);

export const renderReadmeCoverage = (archive: ArchiveManifest): string =>
  `${renderToStaticMarkup(createElement(CoverageOverview, { archive }))}\n`;

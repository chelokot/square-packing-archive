import type { ArchiveManifest, Claim } from "./schema.ts";
import { gridConfiguration } from "./configurations.ts";
import { strongestClaimFor } from "./model.ts";

export type GridBaseline = Pick<Claim, "n" | "value" | "evidence"> & {
  kind: "grid-baseline";
  relation: "upper";
  side: number;
  checkedAt: string;
};

export type ExplorerBound = Claim | GridBaseline;

export const gridBaselineLaw = "Manifest.grid_baseline";

export const isGridBaseline = (bound: ExplorerBound): bound is GridBaseline =>
  "kind" in bound && bound.kind === "grid-baseline";

export const gridBaselineFor = (
  archive: ArchiveManifest,
  count: number,
): GridBaseline | undefined => {
  const policy = archive.gridBaseline;
  if (
    policy === undefined ||
    !Number.isInteger(count) ||
    count < 1 ||
    count > policy.through
  ) {
    return undefined;
  }
  const side = Math.ceil(Math.sqrt(count));
  return {
    kind: "grid-baseline",
    n: count,
    relation: "upper",
    side,
    checkedAt: policy.proof.checkedAt,
    value: {
      decimal: String(side),
      expression: String(side),
      bend: `R.FieldRing.of_nat(~F, ~field, ${side}n)`,
    },
    evidence: [{ ...policy.proof, kind: "bend-proof", status: "bend-checked" }],
  };
};

export const explorerBoundFor = (
  archive: ArchiveManifest,
  count: number,
): ExplorerBound | undefined =>
  strongestClaimFor(archive, count) ?? gridBaselineFor(archive, count);

export const gridBaselineConfiguration = (baseline: GridBaseline) =>
  gridConfiguration(
    `square-${baseline.n}-grid-baseline`,
    baseline.n,
    baseline.side,
    baseline.checkedAt,
  );

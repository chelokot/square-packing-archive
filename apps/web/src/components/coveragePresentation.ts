import type { ExplorerBound } from "@square-packing/domain";
import { copy } from "../copy.ts";

export const coveragePresentation = {
  exact: {
    label: copy.matrixExact,
    className: "border-forest/40 bg-forest-soft text-forest",
    fill: "#e1e9dc",
    ink: "#315d40",
  },
  bound: {
    label: copy.matrixBound,
    className: "border-ochre/40 bg-ochre-soft text-ochre",
    fill: "#f3e8d4",
    ink: "#835c23",
  },
  grid: {
    label: copy.matrixGrid,
    className: "border-rule bg-surface text-muted",
    fill: "#fffef9",
    ink: "#686c62",
  },
} as const;

export const coveragePresentationFor = (bound: ExplorerBound | undefined) => {
  if (bound === undefined) return coveragePresentation.grid;
  if (bound.relation === "exact") return coveragePresentation.exact;
  if (
    bound.relation === "upper" &&
    Number(bound.value.decimal) >= Math.ceil(Math.sqrt(bound.n))
  ) {
    return coveragePresentation.grid;
  }
  return coveragePresentation.bound;
};

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
    className: "border-rule bg-surface text-muted",
    fill: "#fffef9",
    ink: "#686c62",
  },
} as const;

export const coveragePresentationFor = (bound: ExplorerBound | undefined) =>
  coveragePresentation[bound?.relation === "exact" ? "exact" : "bound"];

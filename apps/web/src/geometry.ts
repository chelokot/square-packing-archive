import {
  exactToNumber,
  type PackingConfiguration,
  type Ratio,
  type ExactNumber,
} from "@square-packing/domain";

export const formatRatio = (ratio: Ratio): string =>
  ratio.denominator === "1"
    ? ratio.numerator
    : `${ratio.numerator}/${ratio.denominator}`;

export const formatExact = (value: ExactNumber): string => {
  if ("numerator" in value) return formatRatio(value);
  const rational = formatRatio(value.rational);
  const coefficient = formatRatio(value.sqrtTwo);
  if (coefficient === "0") return rational;
  const radical =
    coefficient === "1"
      ? "√2"
      : coefficient === "-1"
        ? "−√2"
        : `${coefficient}·√2`;
  return rational === "0" ? radical : `${rational} + ${radical}`;
};

export const squareAngle = (
  square: PackingConfiguration["squares"][number],
): number => {
  const angle =
    (Math.atan2(
      exactToNumber(square.orientation.sine),
      exactToNumber(square.orientation.cosine),
    ) *
      180) /
    Math.PI;
  return ((angle % 90) + 90) % 90;
};

export const angleGroup = (angle: number): number =>
  (Math.round(angle * 2) / 2) % 90;
export const clampZoom = (zoom: number): number =>
  Math.min(12, Math.max(0.5, zoom));

export type Viewport = Readonly<{
  panX: number;
  panY: number;
  rotation: number;
  zoom: number;
}>;
export const initialViewport: Viewport = {
  panX: 0,
  panY: 0,
  rotation: 0,
  zoom: 1,
};

export const viewportTransform = (side: number, viewport: Viewport): string =>
  `translate(${side / 2 + viewport.panX} ${side / 2 + viewport.panY}) rotate(${viewport.rotation}) scale(${viewport.zoom}) translate(${-side / 2} ${-side / 2})`;

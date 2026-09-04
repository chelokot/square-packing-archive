import {
  ratioToNumber,
  type PackingConfiguration,
  type Ratio,
} from "@square-packing/domain";

export const formatRatio = (ratio: Ratio): string =>
  ratio.denominator === "1"
    ? ratio.numerator
    : `${ratio.numerator}/${ratio.denominator}`;

export const squareAngle = (
  square: PackingConfiguration["squares"][number],
): number => {
  const angle =
    (Math.atan2(
      ratioToNumber(square.orientation.sine),
      ratioToNumber(square.orientation.cosine),
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

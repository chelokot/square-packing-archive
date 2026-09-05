import {
  exactToNumber,
  type ExplorerBound,
  isGridBaseline,
  type PackingConfiguration,
} from "@square-packing/domain";
import {
  Download,
  Maximize2,
  RotateCcw,
  RotateCw,
  ZoomIn,
  ZoomOut,
} from "lucide-react";
import { useEffect, useMemo, useRef, useState, type PointerEvent } from "react";
import { copy, repositoryUrl } from "../copy.ts";
import {
  angleGroup,
  clampZoom,
  formatExact,
  initialViewport,
  squareAngle,
  viewportTransform,
} from "../geometry.ts";
import { EvidenceBadge } from "./EvidenceBadge.tsx";

const groupColors = [
  "#a8b997",
  "#d7bb82",
  "#a4bac5",
  "#bba9bd",
  "#cdab98",
  "#a0bcb1",
] as const;
type Drag = Readonly<{
  pointerId: number;
  x: number;
  y: number;
  clientX: number;
  clientY: number;
  panX: number;
  panY: number;
  squareId: number | null;
}>;

export const PackingViewer = ({
  configuration,
  claim,
}: {
  configuration: PackingConfiguration;
  claim: ExplorerBound | undefined;
}) => {
  const [viewport, setViewport] = useState(initialViewport);
  const [selectedId, setSelectedId] = useState<number | null>(null);
  const [hiddenGroups, setHiddenGroups] = useState<ReadonlySet<number>>(
    new Set(),
  );
  const [showLabels, setShowLabels] = useState(false);
  const svgRef = useRef<SVGSVGElement>(null);
  const drag = useRef<Drag | null>(null);
  const containerSide = exactToNumber(configuration.containerSide);
  const squareSide = exactToNumber(configuration.squareSide);
  const squares = useMemo(
    () =>
      configuration.squares.map((square) => ({
        ...square,
        angle: squareAngle(square),
        group: angleGroup(squareAngle(square)),
      })),
    [configuration],
  );
  const groups = useMemo(
    () =>
      [...new Set(squares.map((square) => square.group))].sort(
        (left, right) => left - right,
      ),
    [squares],
  );
  const selected = squares.find((square) => square.id === selectedId);
  const proof =
    claim === undefined
      ? undefined
      : claim.evidence.find((evidence) => evidence.kind === "lean-proof");

  const zoom = (factor: number) =>
    setViewport((current) => ({
      ...current,
      zoom: clampZoom(current.zoom * factor),
    }));
  useEffect(() => {
    const svg = svgRef.current!;
    const wheel = (event: WheelEvent) => {
      event.preventDefault();
      setViewport((current) => ({
        ...current,
        zoom: clampZoom(
          current.zoom *
            Math.exp(-Math.max(-100, Math.min(100, event.deltaY)) * 0.002),
        ),
      }));
    };
    svg.addEventListener("wheel", wheel, { passive: false });
    return () => svg.removeEventListener("wheel", wheel);
  }, []);

  const pointerPosition = (event: PointerEvent<SVGSVGElement>) =>
    new DOMPoint(event.clientX, event.clientY).matrixTransform(
      event.currentTarget.getScreenCTM()!.inverse(),
    );
  const pointerDown = (event: PointerEvent<SVGSVGElement>) => {
    if (event.button !== 0 || drag.current !== null) return;
    const point = pointerPosition(event);
    const target =
      event.target instanceof Element
        ? event.target.closest("[data-square-id]")
        : null;
    const squareId =
      target === null ? null : Number(target.getAttribute("data-square-id"));
    drag.current = {
      pointerId: event.pointerId,
      x: point.x,
      y: point.y,
      clientX: event.clientX,
      clientY: event.clientY,
      panX: viewport.panX,
      panY: viewport.panY,
      squareId,
    };
    event.currentTarget.setPointerCapture(event.pointerId);
  };
  const pointerMove = (event: PointerEvent<SVGSVGElement>) => {
    const start = drag.current;
    if (start === null || start.pointerId !== event.pointerId) return;
    const point = pointerPosition(event);
    setViewport((current) => ({
      ...current,
      panX: start.panX + point.x - start.x,
      panY: start.panY + point.y - start.y,
    }));
  };
  const pointerUp = (event: PointerEvent<SVGSVGElement>) => {
    const start = drag.current;
    if (start === null || start.pointerId !== event.pointerId) return;
    if (
      Math.hypot(event.clientX - start.clientX, event.clientY - start.clientY) <
      5
    )
      setSelectedId(start.squareId);
    drag.current = null;
    event.currentTarget.releasePointerCapture(event.pointerId);
  };
  const download = () => {
    const url = URL.createObjectURL(
      new Blob([`${JSON.stringify(configuration, null, 2)}\n`], {
        type: "application/json",
      }),
    );
    const anchor = document.createElement("a");
    anchor.href = url;
    anchor.download = `${configuration.id}.json`;
    anchor.click();
    setTimeout(() => URL.revokeObjectURL(url), 0);
  };
  const controls = [
    { label: copy.zoomOut, icon: ZoomOut, action: () => zoom(1 / 1.2) },
    { label: copy.zoomIn, icon: ZoomIn, action: () => zoom(1.2) },
    {
      label: copy.rotateLeft,
      icon: RotateCcw,
      action: () =>
        setViewport((current) => ({
          ...current,
          rotation: current.rotation - 15,
        })),
    },
    {
      label: copy.rotateRight,
      icon: RotateCw,
      action: () =>
        setViewport((current) => ({
          ...current,
          rotation: current.rotation + 15,
        })),
    },
    {
      label: copy.resetView,
      icon: Maximize2,
      action: () => setViewport(initialViewport),
    },
    { label: copy.download, icon: Download, action: download },
  ];

  return (
    <section
      id="viewer"
      className="overflow-hidden border border-rule bg-surface"
    >
      <div className="flex flex-wrap items-start justify-between gap-4 border-b border-rule px-5 py-4">
        <div>
          <h3 className="font-serif text-2xl">
            {copy.viewerTitle(configuration.n)}
          </h3>
          <p className="mt-1.5 text-xs text-muted">
            {copy.containerSide}{" "}
            <span className="ml-1 font-mono text-ink">
              {configuration.containerSide.decimal}
            </span>
          </p>
        </div>
        <div className="flex flex-wrap gap-1">
          {controls.map(({ label, icon: Icon, action }) => (
            <button
              key={label}
              type="button"
              title={label}
              aria-label={label}
              onClick={action}
              className="grid size-9 place-items-center border border-transparent text-muted hover:border-rule hover:bg-paper hover:text-ink"
            >
              <Icon className="size-4" aria-hidden="true" />
            </button>
          ))}
        </div>
      </div>
      {claim !== undefined && isGridBaseline(claim) && (
        <p className="border-b border-rule bg-paper px-5 py-3 text-xs leading-5 text-muted">
          {copy.gridBaselineNotice}
        </p>
      )}
      <div className="grid 2xl:grid-cols-[minmax(0,1fr)_15rem]">
        <div className="min-w-0">
          <div className="relative aspect-square max-h-[36rem] w-full overflow-hidden p-4">
            <svg
              ref={svgRef}
              viewBox={`${-containerSide * 0.09} ${-containerSide * 0.09} ${containerSide * 1.18} ${containerSide * 1.18}`}
              className="h-full w-full touch-none cursor-grab select-none active:cursor-grabbing"
              onPointerDown={pointerDown}
              onPointerMove={pointerMove}
              onPointerUp={pointerUp}
              onPointerCancel={() => {
                drag.current = null;
              }}
              onLostPointerCapture={() => {
                drag.current = null;
              }}
              role="group"
              aria-label={copy.drawingLabel(configuration.n)}
            >
              <title>{copy.drawingLabel(configuration.n)}</title>
              <g
                data-testid="packing-transform"
                transform={viewportTransform(containerSide, viewport)}
              >
                <rect
                  width={containerSide}
                  height={containerSide}
                  fill="var(--color-surface)"
                  stroke="var(--color-ink)"
                  strokeWidth="1"
                  vectorEffect="non-scaling-stroke"
                />
                {squares
                  .filter((square) => !hiddenGroups.has(square.group))
                  .map((square) => {
                    const active = square.id === selectedId;
                    return (
                      <g
                        key={square.id}
                        transform={`translate(${exactToNumber(square.center.x)} ${containerSide - exactToNumber(square.center.y)}) rotate(${-square.angle})`}
                      >
                        <rect
                          data-square-id={square.id}
                          x={-squareSide / 2}
                          y={-squareSide / 2}
                          width={squareSide}
                          height={squareSide}
                          fill={
                            groupColors[
                              groups.indexOf(square.group) % groupColors.length
                            ]
                          }
                          fillOpacity={active ? 1 : 0.7}
                          stroke={
                            active ? "var(--color-forest)" : "var(--color-ink)"
                          }
                          strokeWidth={active ? 2.5 : 0.7}
                          vectorEffect="non-scaling-stroke"
                          role="button"
                          aria-label={copy.square(square.id)}
                          aria-pressed={active}
                          tabIndex={0}
                          onClick={(event) => {
                            if (event.detail === 0) setSelectedId(square.id);
                          }}
                          onKeyDown={(event) => {
                            if (event.key === "Enter" || event.key === " ") {
                              event.preventDefault();
                              setSelectedId(square.id);
                            }
                          }}
                          className="cursor-pointer hover:fill-opacity-100"
                        >
                          <title>
                            {copy.square(square.id)} · {square.angle.toFixed(3)}
                            °
                          </title>
                        </rect>
                        {showLabels ? (
                          <text
                            x="0"
                            y="0"
                            textAnchor="middle"
                            dominantBaseline="central"
                            fontSize={squareSide * 0.21}
                            fill="var(--color-ink)"
                            className="pointer-events-none font-mono"
                          >
                            {square.id}
                          </text>
                        ) : null}
                      </g>
                    );
                  })}
              </g>
            </svg>
            <output
              aria-live="polite"
              className="pointer-events-none absolute bottom-4 left-5 border border-rule bg-surface/90 px-2 py-1 font-mono text-[0.65rem] text-muted"
            >
              {viewport.zoom.toFixed(2)}× · {viewport.rotation}°
            </output>
          </div>
          <div className="flex flex-wrap items-center justify-between gap-3 border-t border-rule px-5 py-3 text-[0.65rem] text-muted">
            <p>{copy.viewHelp}</p>
            <label className="flex cursor-pointer items-center gap-2">
              <input
                type="checkbox"
                checked={showLabels}
                onChange={(event) => setShowLabels(event.target.checked)}
                className="accent-forest"
              />
              {copy.showLabels}
            </label>
          </div>
        </div>
        <aside className="min-w-0 border-t border-rule bg-paper/50 p-5 2xl:border-l 2xl:border-t-0">
          <h4 className="text-xs font-medium">{copy.angleGroups}</h4>
          <p className="mt-1 text-[0.65rem] leading-5 text-muted">
            {copy.angleGroupHelp}
          </p>
          <div className="mt-3 flex flex-wrap gap-2">
            {groups.map((group, index) => (
              <button
                key={group}
                type="button"
                aria-pressed={!hiddenGroups.has(group)}
                onClick={() =>
                  setHiddenGroups((current) => {
                    const next = new Set(current);
                    if (next.has(group)) next.delete(group);
                    else next.add(group);
                    return next;
                  })
                }
                className={`flex items-center gap-1.5 border border-rule px-2 py-1 font-mono text-[0.65rem] ${hiddenGroups.has(group) ? "text-muted line-through" : "bg-surface text-ink"}`}
              >
                <i
                  className="size-2.5"
                  style={{
                    backgroundColor: groupColors[index % groupColors.length],
                  }}
                />
                {group.toFixed(1)}°{" "}
                <span className="text-muted">
                  ({squares.filter((square) => square.group === group).length})
                </span>
              </button>
            ))}
          </div>
          <div className="mt-5 border-t border-rule pt-4">
            <label htmlFor="square-selection" className="text-xs font-medium">
              {copy.selectSquare}
            </label>
            <select
              id="square-selection"
              value={selectedId === null ? "" : selectedId}
              onChange={(event) =>
                setSelectedId(
                  event.target.value === "" ? null : Number(event.target.value),
                )
              }
              className="mt-2 w-full border border-rule bg-surface p-2 text-xs"
            >
              <option value="">{copy.noSquare}</option>
              {squares.map((square) => (
                <option key={square.id} value={square.id}>
                  {copy.square(square.id)}
                </option>
              ))}
            </select>
            {selected === undefined ? (
              <p className="mt-4 text-xs leading-6 text-muted">
                {copy.inspectPrompt}
              </p>
            ) : (
              <div className="mt-4">
                <h4 className="flex items-baseline justify-between gap-2 text-sm font-medium">
                  {copy.square(selected.id)}
                  <span className="font-mono text-[0.65rem] text-muted">
                    {selected.angle.toFixed(6)}°
                  </span>
                </h4>
                <dl className="mt-3 space-y-3 text-xs">
                  {[
                    { label: copy.centerX, value: selected.center.x },
                    { label: copy.centerY, value: selected.center.y },
                  ].map(({ label, value }) => (
                    <div key={label}>
                      <dt className="text-muted">{label}</dt>
                      <dd className="mt-1 break-all font-mono">
                        {exactToNumber(value).toFixed(12)}
                      </dd>
                    </div>
                  ))}
                </dl>
                <details className="mt-4 text-xs" open>
                  <summary className="text-forest">
                    {copy.exactCoordinates}
                  </summary>
                  <dl className="mt-3 space-y-3">
                    {[
                      { label: copy.centerX, value: selected.center.x },
                      { label: copy.centerY, value: selected.center.y },
                      {
                        label: copy.tangent,
                        value: selected.orientation.tangentHalfAngle,
                      },
                      {
                        label: copy.cosine,
                        value: selected.orientation.cosine,
                      },
                      { label: copy.sine, value: selected.orientation.sine },
                    ].map(({ label, value }) => (
                      <div key={label}>
                        <dt className="text-muted">{label}</dt>
                        <dd className="mt-1 break-all font-mono text-[0.65rem] leading-5">
                          {formatExact(value)}
                        </dd>
                      </div>
                    ))}
                  </dl>
                </details>
              </div>
            )}
          </div>
        </aside>
      </div>
      <div className="flex flex-wrap items-center gap-3 border-t border-rule px-5 py-3">
        {claim === undefined ? null : <EvidenceBadge claim={claim} />}
        <p className="flex-1 text-[0.65rem] leading-5 text-muted">
          {copy.layoutBound}
        </p>
        {proof === undefined ? null : (
          <a
            className="text-xs text-forest underline decoration-forest/30 underline-offset-4"
            href={`${repositoryUrl}/blob/main/${proof.artifact}`}
            title={proof.theorem}
          >
            {copy.proof}
          </a>
        )}
      </div>
    </section>
  );
};

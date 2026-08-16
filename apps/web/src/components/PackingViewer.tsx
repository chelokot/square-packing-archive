import {
  ratioToNumber,
  type PackingConfiguration,
} from "@square-packing/domain";
import {
  Crosshair,
  Download,
  Maximize2,
  RotateCcw,
  RotateCw,
  ZoomIn,
  ZoomOut,
} from "lucide-react";
import {
  useMemo,
  useRef,
  useState,
  type PointerEvent,
  type WheelEvent,
} from "react";

type Viewport = Readonly<{
  panX: number;
  panY: number;
  rotation: number;
  zoom: number;
}>;

const initialViewport: Viewport = { panX: 0, panY: 0, rotation: 0, zoom: 1 };
const colors = [
  "#62f5c8",
  "#70ddff",
  "#b9a4ff",
  "#ffc66d",
  "#ff8fa3",
  "#77a7ff",
] as const;

const degrees = (radians: number): number =>
  ((((radians * 180) / Math.PI) % 90) + 90) % 90;

const angleGroup = (radians: number): number =>
  Math.round(degrees(radians) * 2) / 2;

const formatRatio = (ratio: {
  numerator: string;
  denominator: string;
}): string =>
  ratio.denominator === "1"
    ? ratio.numerator
    : `${ratio.numerator}/${ratio.denominator}`;

export const PackingViewer = ({
  configuration,
}: {
  configuration: PackingConfiguration;
}) => {
  const [viewport, setViewport] = useState(initialViewport);
  const [selectedSquare, setSelectedSquare] = useState<number | null>(null);
  const [hiddenGroups, setHiddenGroups] = useState<ReadonlySet<number>>(
    new Set(),
  );
  const dragOrigin = useRef<{
    x: number;
    y: number;
    panX: number;
    panY: number;
  } | null>(null);
  const containerSide = ratioToNumber(configuration.containerSide);
  const groups = useMemo(
    () =>
      [
        ...new Set(
          configuration.squares.map((square) =>
            angleGroup(square.orientation.angleRadiansApprox),
          ),
        ),
      ].sort((left, right) => left - right),
    [configuration],
  );
  const selected = configuration.squares.find(
    (square) => square.id === selectedSquare,
  );

  const updateZoom = (factor: number) =>
    setViewport((current) => ({
      ...current,
      zoom: Math.min(8, Math.max(0.5, current.zoom * factor)),
    }));

  const handlePointerDown = (event: PointerEvent<SVGSVGElement>) => {
    event.currentTarget.setPointerCapture(event.pointerId);
    dragOrigin.current = {
      x: event.clientX,
      y: event.clientY,
      panX: viewport.panX,
      panY: viewport.panY,
    };
  };

  const handlePointerMove = (event: PointerEvent<SVGSVGElement>) => {
    if (dragOrigin.current === null) {
      return;
    }
    const scale = containerSide / (480 * viewport.zoom);
    setViewport((current) => ({
      ...current,
      panX:
        dragOrigin.current!.panX +
        (event.clientX - dragOrigin.current!.x) * scale,
      panY:
        dragOrigin.current!.panY +
        (event.clientY - dragOrigin.current!.y) * scale,
    }));
  };

  const handlePointerUp = () => {
    dragOrigin.current = null;
  };

  const handleWheel = (event: WheelEvent<SVGSVGElement>) => {
    event.preventDefault();
    updateZoom(event.deltaY < 0 ? 1.12 : 1 / 1.12);
  };

  const download = () => {
    const blob = new Blob([`${JSON.stringify(configuration, null, 2)}\n`], {
      type: "application/json",
    });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement("a");
    anchor.href = url;
    anchor.download = `${configuration.id}.json`;
    anchor.click();
    URL.revokeObjectURL(url);
  };

  return (
    <section
      id="viewer"
      className="overflow-hidden rounded-3xl border border-white/10 bg-ink-900/80 shadow-2xl shadow-black/30"
    >
      <div className="flex flex-col gap-4 border-b border-white/10 px-5 py-4 sm:flex-row sm:items-center sm:justify-between">
        <div>
          <p className="font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
            Interactive certificate
          </p>
          <h2 className="mt-1 text-xl font-semibold text-white">
            {configuration.n} unit squares · side{" "}
            {configuration.containerSide.decimal}
          </h2>
        </div>
        <div className="flex flex-wrap gap-2">
          {[
            {
              label: "Zoom out",
              icon: ZoomOut,
              action: () => updateZoom(1 / 1.2),
            },
            { label: "Zoom in", icon: ZoomIn, action: () => updateZoom(1.2) },
            {
              label: "Rotate left",
              icon: RotateCcw,
              action: () =>
                setViewport((current) => ({
                  ...current,
                  rotation: current.rotation - 15,
                })),
            },
            {
              label: "Rotate right",
              icon: RotateCw,
              action: () =>
                setViewport((current) => ({
                  ...current,
                  rotation: current.rotation + 15,
                })),
            },
            {
              label: "Reset view",
              icon: Maximize2,
              action: () => setViewport(initialViewport),
            },
            { label: "Download data", icon: Download, action: download },
          ].map(({ label, icon: Icon, action }) => (
            <button
              key={label}
              type="button"
              title={label}
              onClick={action}
              className="grid size-9 place-items-center rounded-xl border border-white/10 bg-white/5 text-slate-300 transition hover:border-cyan-300/40 hover:bg-cyan-300/10 hover:text-cyan-300"
            >
              <Icon className="size-4" aria-hidden="true" />
              <span className="sr-only">{label}</span>
            </button>
          ))}
        </div>
      </div>
      <div className="grid lg:grid-cols-[minmax(0,1fr)_19rem]">
        <div className="relative min-h-[32rem] overflow-hidden bg-[radial-gradient(circle_at_center,rgba(112,221,255,.08),transparent_60%)] p-4">
          <svg
            viewBox={`${-containerSide * 0.08} ${-containerSide * 0.08} ${containerSide * 1.16} ${containerSide * 1.16}`}
            className="h-full min-h-[30rem] w-full cursor-grab touch-none active:cursor-grabbing"
            onPointerDown={handlePointerDown}
            onPointerMove={handlePointerMove}
            onPointerUp={handlePointerUp}
            onPointerCancel={handlePointerUp}
            onWheel={handleWheel}
            role="img"
            aria-label={`Packing of ${configuration.n} unit squares`}
          >
            <defs>
              <filter
                id="selected-glow"
                x="-100%"
                y="-100%"
                width="300%"
                height="300%"
              >
                <feGaussianBlur stdDeviation="0.06" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>
            </defs>
            <g
              transform={`translate(${containerSide / 2 + viewport.panX} ${containerSide / 2 + viewport.panY}) rotate(${viewport.rotation}) scale(${viewport.zoom}) translate(${-containerSide / 2} ${-containerSide / 2})`}
            >
              <rect
                x="0"
                y="0"
                width={containerSide}
                height={containerSide}
                rx={containerSide * 0.015}
                fill="#07111f"
                stroke="rgba(255,255,255,.35)"
                strokeWidth={containerSide * 0.012}
              />
              {configuration.squares.map((square) => {
                const group = angleGroup(square.orientation.angleRadiansApprox);
                if (hiddenGroups.has(group)) {
                  return null;
                }
                const centerX = ratioToNumber(square.center.x);
                const centerY = containerSide - ratioToNumber(square.center.y);
                const active = square.id === selectedSquare;
                return (
                  <rect
                    key={square.id}
                    x="-0.5"
                    y="-0.5"
                    width="1"
                    height="1"
                    rx="0.025"
                    transform={`translate(${centerX} ${centerY}) rotate(${-degrees(square.orientation.angleRadiansApprox)})`}
                    fill={colors[groups.indexOf(group) % colors.length]}
                    fillOpacity={active ? 0.95 : 0.68}
                    stroke={active ? "#ffffff" : "rgba(5,11,20,.8)"}
                    strokeWidth={active ? 0.045 : 0.018}
                    vectorEffect="non-scaling-stroke"
                    filter={active ? "url(#selected-glow)" : undefined}
                    onPointerDown={(event) => {
                      event.stopPropagation();
                      setSelectedSquare(square.id);
                    }}
                    className="cursor-pointer transition-opacity hover:opacity-100"
                  />
                );
              })}
            </g>
          </svg>
          <div className="pointer-events-none absolute bottom-6 left-6 rounded-full border border-white/10 bg-ink-950/80 px-3 py-1.5 font-mono text-[0.68rem] text-slate-400 backdrop-blur">
            {viewport.zoom.toFixed(2)}× · {viewport.rotation}°
          </div>
        </div>
        <aside className="border-t border-white/10 bg-black/10 p-5 lg:border-l lg:border-t-0">
          <p className="font-mono text-[0.68rem] uppercase tracking-[0.2em] text-slate-500">
            Angle groups
          </p>
          <div className="mt-3 flex flex-wrap gap-2">
            {groups.map((group, index) => {
              const hidden = hiddenGroups.has(group);
              const count = configuration.squares.filter(
                (square) =>
                  angleGroup(square.orientation.angleRadiansApprox) === group,
              ).length;
              return (
                <button
                  key={group}
                  type="button"
                  onClick={() =>
                    setHiddenGroups((current) => {
                      const next = new Set(current);
                      if (next.has(group)) next.delete(group);
                      else next.add(group);
                      return next;
                    })
                  }
                  className={`rounded-full border px-2.5 py-1 font-mono text-[0.68rem] transition ${hidden ? "border-white/10 text-slate-600 line-through" : "border-white/15 text-slate-200"}`}
                >
                  <i
                    className="mr-1.5 inline-block size-2 rounded-full"
                    style={{ backgroundColor: colors[index % colors.length] }}
                  />
                  {group.toFixed(1)}° · {count}
                </button>
              );
            })}
          </div>
          <div className="my-5 h-px bg-white/10" />
          {selected === undefined ? (
            <div className="grid min-h-48 place-items-center text-center">
              <div>
                <Crosshair className="mx-auto size-6 text-slate-600" />
                <p className="mt-3 text-sm text-slate-500">
                  Select a square to inspect its exact coordinates.
                </p>
              </div>
            </div>
          ) : (
            <div>
              <div className="flex items-center justify-between">
                <h3 className="font-semibold text-white">
                  Square {selected.id}
                </h3>
                <span className="font-mono text-xs text-cyan-300">
                  {degrees(selected.orientation.angleRadiansApprox).toFixed(6)}°
                </span>
              </div>
              <dl className="mt-4 space-y-4 text-xs">
                <div>
                  <dt className="text-slate-500">Center x</dt>
                  <dd className="mt-1 break-all font-mono text-slate-200">
                    {ratioToNumber(selected.center.x).toFixed(12)}
                  </dd>
                </div>
                <div>
                  <dt className="text-slate-500">Center y</dt>
                  <dd className="mt-1 break-all font-mono text-slate-200">
                    {ratioToNumber(selected.center.y).toFixed(12)}
                  </dd>
                </div>
                <div>
                  <dt className="text-slate-500">Exact t = tan(θ/2)</dt>
                  <dd className="mt-1 break-all font-mono leading-5 text-slate-200">
                    {formatRatio(selected.orientation.tangentHalfAngle)}
                  </dd>
                </div>
                <div>
                  <dt className="text-slate-500">Exact cos θ</dt>
                  <dd className="mt-1 break-all font-mono leading-5 text-slate-200">
                    {formatRatio(selected.orientation.cosine)}
                  </dd>
                </div>
                <div>
                  <dt className="text-slate-500">Exact sin θ</dt>
                  <dd className="mt-1 break-all font-mono leading-5 text-slate-200">
                    {formatRatio(selected.orientation.sine)}
                  </dd>
                </div>
              </dl>
            </div>
          )}
        </aside>
      </div>
    </section>
  );
};

import { activeClaims, isVerified } from "@square-packing/domain";
import { Github, Grid3X3, Menu, Sigma, X } from "lucide-react";
import { useState } from "react";
import { archive } from "./archive.ts";
import { ClaimsTable } from "./components/ClaimsTable.tsx";
import { CoverageChart } from "./components/CoverageChart.tsx";
import { CoverageMatrix } from "./components/CoverageMatrix.tsx";
import { FormalizationPanel } from "./components/FormalizationPanel.tsx";
import { PackingViewer } from "./components/PackingViewer.tsx";
import { RecordTimeline } from "./components/RecordTimeline.tsx";

const links = [
  { label: "Matrix", href: "#matrix" },
  { label: "Viewer", href: "#viewer" },
  { label: "Claims", href: "#claims" },
  { label: "Formalization", href: "#formalization" },
] as const;

const Stat = ({
  label,
  value,
  accent,
}: {
  label: string;
  value: string;
  accent: string;
}) => (
  <div className="rounded-2xl border border-white/10 bg-white/[0.035] p-4 backdrop-blur">
    <div className={`font-mono text-2xl font-semibold ${accent}`}>{value}</div>
    <div className="mt-1 text-xs text-slate-500">{label}</div>
  </div>
);

export const App = () => {
  const [menuOpen, setMenuOpen] = useState(false);
  const [selectedCount, setSelectedCount] = useState(68);
  const [configurationId, setConfigurationId] = useState("square-68");
  const currentClaims = activeClaims(archive);
  const exactClaims = currentClaims.filter(
    (claim) => claim.relation === "exact",
  );
  const verifiedClaims = currentClaims.filter(isVerified);
  const configuration = archive.configurationData.find(
    ({ id }) => id === configurationId,
  );
  if (configuration === undefined) {
    throw new Error(`Missing configuration ${configurationId}`);
  }

  return (
    <div className="min-h-screen overflow-hidden bg-ink-950 text-slate-200">
      <div className="pointer-events-none fixed inset-0 bg-[radial-gradient(circle_at_15%_5%,rgba(112,221,255,.12),transparent_28%),radial-gradient(circle_at_86%_18%,rgba(185,164,255,.10),transparent_25%)]" />
      <header className="sticky top-0 z-50 border-b border-white/[0.07] bg-ink-950/80 backdrop-blur-xl">
        <div className="mx-auto flex max-w-[90rem] items-center justify-between px-5 py-3 md:px-8">
          <a href="#top" className="flex items-center gap-3">
            <span className="grid size-9 place-items-center rounded-xl border border-mint-300/30 bg-mint-300/10">
              <Grid3X3 className="size-4 text-mint-300" />
            </span>
            <span>
              <b className="block text-sm text-white">Square Packing</b>
              <span className="block font-mono text-[0.6rem] uppercase tracking-[0.2em] text-slate-500">
                Formal archive
              </span>
            </span>
          </a>
          <nav className="hidden items-center gap-7 md:flex">
            {links.map((link) => (
              <a
                key={link.href}
                href={link.href}
                className="text-xs font-medium text-slate-400 transition hover:text-white"
              >
                {link.label}
              </a>
            ))}
          </nav>
          <div className="flex items-center gap-2">
            <a
              href="https://github.com/chelokot/square-packing-archive"
              target="_blank"
              rel="noreferrer"
              className="grid size-9 place-items-center rounded-xl border border-white/10 text-slate-300 transition hover:border-white/25 hover:text-white"
            >
              <Github className="size-4" />
              <span className="sr-only">GitHub</span>
            </a>
            <button
              type="button"
              className="grid size-9 place-items-center rounded-xl border border-white/10 md:hidden"
              onClick={() => setMenuOpen((open) => !open)}
            >
              {menuOpen ? (
                <X className="size-4" />
              ) : (
                <Menu className="size-4" />
              )}
              <span className="sr-only">Toggle navigation</span>
            </button>
          </div>
        </div>
        {menuOpen ? (
          <nav className="border-t border-white/10 px-5 py-3 md:hidden">
            {links.map((link) => (
              <a
                key={link.href}
                href={link.href}
                onClick={() => setMenuOpen(false)}
                className="block py-2 text-sm text-slate-300"
              >
                {link.label}
              </a>
            ))}
          </nav>
        ) : null}
      </header>

      <main
        id="top"
        className="relative mx-auto max-w-[90rem] px-5 pb-20 md:px-8"
      >
        <section className="grid min-h-[38rem] items-center gap-12 py-16 lg:grid-cols-[1.1fr_0.9fr] lg:py-24">
          <div>
            <div className="mb-6 inline-flex items-center gap-2 rounded-full border border-cyan-300/20 bg-cyan-300/[0.06] px-3 py-1.5 font-mono text-[0.68rem] uppercase tracking-[0.16em] text-cyan-300">
              <Sigma className="size-3.5" /> One source of truth · zero
              ambiguous badges
            </div>
            <h1 className="max-w-4xl text-5xl font-semibold leading-[0.98] tracking-[-0.045em] text-white sm:text-6xl lg:text-7xl">
              Every packing.
              <br />
              <span className="bg-gradient-to-r from-mint-300 via-cyan-300 to-violet-300 bg-clip-text text-transparent">
                Every claim. Checkable.
              </span>
            </h1>
            <p className="mt-7 max-w-2xl text-base leading-7 text-slate-400 md:text-lg md:leading-8">
              A provenance-first archive for packing congruent unit squares in a
              square: historical records, exact coordinates, interactive
              geometry, publications, and Lean proofs connected by one canonical
              dataset.
            </p>
            <div className="mt-8 flex flex-wrap gap-3">
              <a
                href="#viewer"
                className="rounded-full bg-mint-300 px-5 py-2.5 text-sm font-semibold text-ink-950 transition hover:bg-white"
              >
                Open the viewer
              </a>
              <a
                href="#formalization"
                className="rounded-full border border-white/15 px-5 py-2.5 text-sm font-semibold text-white transition hover:border-white/30 hover:bg-white/5"
              >
                How verification works
              </a>
            </div>
          </div>
          <div className="grid grid-cols-2 gap-3 lg:pl-10">
            <Stat
              label="Curated claims"
              value={String(archive.claims.length)}
              accent="text-cyan-300"
            />
            <Stat
              label="Published exact n"
              value={String(new Set(exactClaims.map((claim) => claim.n)).size)}
              accent="text-amber-300"
            />
            <Stat
              label="Lean-verified claims"
              value={String(verifiedClaims.length)}
              accent="text-mint-300"
            />
            <Stat
              label="Exact rational layouts"
              value={String(archive.configurationData.length)}
              accent="text-violet-300"
            />
            <div className="col-span-2 rounded-2xl border border-white/10 bg-[linear-gradient(120deg,rgba(98,245,200,.08),rgba(112,221,255,.03))] p-5">
              <div className="font-mono text-[0.68rem] uppercase tracking-[0.18em] text-slate-500">
                Definition
              </div>
              <p className="mt-3 text-sm leading-6 text-slate-300">
                {archive.problem.definition}
              </p>
            </div>
          </div>
        </section>

        <div className="grid gap-6 xl:grid-cols-[1.08fr_0.92fr]">
          <CoverageMatrix
            archive={archive}
            selectedCount={selectedCount}
            onSelect={setSelectedCount}
          />
          <div className="grid gap-6">
            <CoverageChart archive={archive} />
            <RecordTimeline archive={archive} squareCount={selectedCount} />
          </div>
        </div>

        <section className="mt-20">
          <div className="mb-6 flex flex-col justify-between gap-4 sm:flex-row sm:items-end">
            <div>
              <p className="font-mono text-xs uppercase tracking-[0.22em] text-cyan-300">
                Geometry laboratory
              </p>
              <h2 className="mt-2 text-3xl font-semibold tracking-tight text-white">
                Inspect the certificate, not a screenshot
              </h2>
            </div>
            <div className="flex rounded-full border border-white/10 bg-white/[0.03] p-1">
              {archive.configurationData.map((item) => (
                <button
                  key={item.id}
                  type="button"
                  onClick={() => setConfigurationId(item.id)}
                  className={`rounded-full px-4 py-2 font-mono text-xs transition ${configurationId === item.id ? "bg-white text-ink-950" : "text-slate-400 hover:text-white"}`}
                >
                  n={item.n}
                </button>
              ))}
            </div>
          </div>
          <PackingViewer key={configuration.id} configuration={configuration} />
        </section>

        <div className="mt-20">
          <ClaimsTable archive={archive} />
        </div>
        <div className="mt-20">
          <FormalizationPanel archive={archive} />
        </div>
      </main>

      <footer className="relative border-t border-white/[0.07] bg-black/10">
        <div className="mx-auto flex max-w-[90rem] flex-col gap-3 px-5 py-8 text-xs text-slate-500 sm:flex-row sm:items-center sm:justify-between md:px-8">
          <p>
            Code & Lean: Apache-2.0 · Data & original visualizations: CC BY 4.0
          </p>
          <p>
            Built with gratitude to Friedman, Ellsworth, and every contributor
            in the record lineage.
          </p>
        </div>
      </footer>
    </div>
  );
};

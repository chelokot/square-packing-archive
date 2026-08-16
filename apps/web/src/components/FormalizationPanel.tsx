import type { CompiledArchive } from "@square-packing/domain";
import {
  ArrowRight,
  CheckCircle2,
  CircleDotDashed,
  GitPullRequest,
  ShieldCheck,
} from "lucide-react";

const stages = [
  {
    title: "Canonical claim",
    detail:
      "Value, authors, date, source, and complete provenance enter the manifest.",
    icon: CircleDotDashed,
  },
  {
    title: "Exact certificate",
    detail:
      "Coordinates and orientations are rationalized without floating-point trust.",
    icon: ShieldCheck,
  },
  {
    title: "Lean theorem",
    detail:
      "The kernel checks containment, separation, and the claimed relation.",
    icon: CheckCircle2,
  },
  {
    title: "Reproducible merge",
    detail:
      "CI regenerates the site; the PR becomes an immutable historical event.",
    icon: GitPullRequest,
  },
] as const;

export const FormalizationPanel = ({
  archive,
}: {
  archive: CompiledArchive;
}) => (
  <section
    id="formalization"
    className="rounded-3xl border border-mint-300/20 bg-[linear-gradient(135deg,rgba(98,245,200,.09),rgba(112,221,255,.03)_45%,rgba(185,164,255,.07))] p-5 md:p-8"
  >
    <div className="grid gap-9 xl:grid-cols-[0.85fr_1.15fr] xl:items-center">
      <div>
        <p className="font-mono text-xs uppercase tracking-[0.22em] text-mint-300">
          Trust model
        </p>
        <h2 className="mt-3 max-w-xl text-3xl font-semibold tracking-tight text-white md:text-4xl">
          Nothing is “verified” until Lean says so.
        </h2>
        <p className="mt-4 max-w-xl text-sm leading-7 text-slate-300">
          The archive can respect a published proof without silently treating it
          as machine-checked. Verification is a property of an exact theorem and
          its dependency closure, never a badge assigned by an editor.
        </p>
        <a
          href="https://github.com/chelokot/square-packing-archive/tree/main/formal"
          className="mt-6 inline-flex items-center gap-2 rounded-full border border-mint-300/35 bg-mint-300/10 px-4 py-2 text-sm font-semibold text-mint-300 transition hover:bg-mint-300/15"
        >
          Explore Lean sources{" "}
          <ArrowRight className="size-4" aria-hidden="true" />
        </a>
      </div>
      <ol className="grid gap-3 sm:grid-cols-2">
        {stages.map(({ title, detail, icon: Icon }, index) => (
          <li
            key={title}
            className="rounded-2xl border border-white/10 bg-ink-950/45 p-4 backdrop-blur"
          >
            <div className="flex items-center gap-3">
              <span className="grid size-8 place-items-center rounded-xl bg-white/[0.07] font-mono text-xs text-slate-500">
                0{index + 1}
              </span>
              <Icon className="size-4 text-mint-300" aria-hidden="true" />
            </div>
            <h3 className="mt-4 font-semibold text-white">{title}</h3>
            <p className="mt-2 text-xs leading-5 text-slate-400">{detail}</p>
          </li>
        ))}
      </ol>
    </div>
    <p className="mt-7 border-t border-white/10 pt-5 font-mono text-[0.68rem] uppercase tracking-[0.16em] text-slate-500">
      Schema v{archive.schemaVersion} · generated from archive/manifest.json ·
      no hand-maintained dashboard data
    </p>
  </section>
);

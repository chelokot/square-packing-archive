# Square Packing Archive

[![CI](https://github.com/chelokot/square-packing-archive/actions/workflows/ci.yml/badge.svg)](https://github.com/chelokot/square-packing-archive/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-62f5c8)](formal/lean-toolchain)
[![Code license](https://img.shields.io/badge/code-Apache--2.0-70ddff)](LICENSE)
[![Data license](https://img.shields.io/badge/data-CC%20BY%204.0-b9a4ff)](LICENSE-DATA)

Square Packing Archive is a provenance-first, machine-verifiable record of the
problem of packing congruent unit squares into the smallest square container.
It connects historical claims, authors, publications, exact coordinates,
interactive visualizations, computational certificates, and Lean theorems
without conflating them.

The project uses one strict rule: **verified means checked by Lean**. A
peer-reviewed proof is represented as `published · awaiting Lean`; a robust
interval or rational computation is `computed · awaiting Lean`. This preserves
the literature faithfully while making the formalization gap measurable.

## What is live

- A versioned canonical manifest with claims, authors, sources, provenance, and
  immutable record lineage.
- Curated historical exact results below 100 and selected historical upper-bound
  progressions.
- Lean-verified exact rational certificates for the archive's new upper bounds
  `s(68) ≤ 8.80339` and `s(69) ≤ 8.8272`.
- A Lean geometry model, a formal area theorem, a proof that `s(m²) = m` for
  every `m`, and a rational separating-axis certificate checker with a proved
  soundness theorem.
- A generated dashboard with a proof matrix, historical coverage graph, record
  timelines, source links, and an interactive packing viewer.
- Viewer controls for zoom, pan, view rotation, square inspection, exact
  coordinates, and filtering by orientation group.
- A shared `?n=` selection across the matrix, viewer, and record history;
  searchable evidence and author filters; accessible square inspection.
- Separate publication and Lean check dates. Historical coverage uses the
  date each proof was recorded as checked, rather than its publication year.

The historical catalog is intentionally incomplete at the first release. Missing
records are visible as missing; import work never invents metadata or silently
upgrades evidence.

## Architecture

```text
archive/
  manifest.json                 canonical metadata and record lineage
  configurations/              exact rational packing certificates
apps/web/                       generated React dashboard and SVG viewer
packages/domain/                schema, validation, and pure derived views
formal/SquarePackingArchive/    definitions, sound checker, and Lean theorems
scripts/                        deterministic import and code generation
```

`archive/manifest.json` and its referenced configuration files are the only
editable source of archive facts. The web bundle is generated from them. Lean
record modules are also generated from the same rational configurations, while
their shared soundness proof is maintained by hand.

## Trust model

| Display status              | Meaning                                                    |
| --------------------------- | ---------------------------------------------------------- |
| `Reported`                  | A tracker or source reports the claim.                     |
| `Computed · awaiting Lean`  | An independent computational certificate exists.           |
| `Published · awaiting Lean` | A mathematical proof is published but not formalized here. |
| `Lean verified`             | Lean CI checks the exact theorem without `sorry`.          |

Only the final row contributes to verified counters and graphs.

## Development

Install [Bun](https://bun.sh/) and [elan](https://github.com/leanprover/elan),
then run:

```console
bun install
bun run archive:build
bun run check
bun run test
bun run build

cd formal
lake update
lake exe cache get
lake build
```

The web application runs locally with:

```console
bun run dev
```

The optional private Sites preview uses the same app, built at the origin root:

```console
bun run site:package
```

This produces `dist/site.tar.gz` containing only the built static site and its
Sites deployment metadata. The normal build retains the GitHub Pages base path.
The static packaging script follows the Sites archive contract; the bundled
Worker-only packaging helper and Vite 8 plugin are not used by this Vite 7 app.

The social-preview artwork at `apps/web/public/og.png` was generated with the
built-in imagegen tool using the prompt recorded in [the artwork notes](docs/site-artwork.md).

## Reproducible imports

The archive's two initial computational records are imported from the companion
research workspace and reconstructed with exact rational orientations:

```console
python scripts/import-research-records.py \
  ../square-packing-research/records/square-68.json \
  archive/configurations/square-68.json

python scripts/generate-lean-certificates.py \
  archive/configurations/square-68.json \
  formal/SquarePackingArchive/Records/Square68.lean
```

The importer replaces every floating angle with a rational tangent-half-angle.
Consequently, `sin θ`, `cos θ`, containment, and all separating axes are exact
rational expressions inside Lean.

## Sources and gratitude

The initial historical catalog is grounded in
[Erich Friedman's survey](https://doi.org/10.37236/28) and the current
[Squares in Squares tracker](https://kingbird.myphotos.cc/packing/squares_in_squares.html),
whose high-precision SVG work is maintained by David Ellsworth. The archive is
not a replacement for either: it is the formal, structured layer their work
makes possible. Every individual result retains discoverer, optimizer, prover,
date, and source roles where available.

See [ATTRIBUTION.md](ATTRIBUTION.md) and [CONTRIBUTING.md](CONTRIBUTING.md).
Source-specific corrections discovered during formalization are recorded in
[the Nagamochi 2005 notes](docs/nagamochi-2005-formalization.md). The reusable
finite-piercing reduction and its current geometric coverage are tracked in
[the Friedman unavoidable-point notes](docs/friedman-unavoidable-formalization.md).

## License

Code, generators, the web application, and Lean sources are available under
Apache-2.0. Canonical metadata, original prose, and original generated
visualizations are available under CC BY 4.0. Linked publications and external
sites remain under their own terms.

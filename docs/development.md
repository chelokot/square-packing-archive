# Development

For the problem, selected results, and public site, start with the [README](../README.md).
For submission requirements, see [CONTRIBUTING.md](../CONTRIBUTING.md).

## Architecture

```text
archive/
  manifest.json                 claims, contributors, sources, and record lineage
  configurations/              exact packing coordinates and certificates
apps/web/                       React dashboard and SVG packing viewer
packages/domain/                schema, validation, and pure derived views
formal/SquarePackingArchive/    geometry, certificate checker, and Lean proofs
scripts/                        imports, code generation, and consistency checks
```

The [manifest](../archive/manifest.json) and its referenced configuration files
are the editable source of archive data. The web bundle and README matrix are
generated with `bun run archive:build`; `bun run archive:check` rejects a stale
matrix. Both views use the same claim-selection rules.

Rational certificate modules are generated from configuration data. Geometric
proofs and the certificate checker's soundness theorem are maintained separately;
they are not generated from metadata. The evidence generator produces typed
checks and dependency-axiom assertions for the manifest's linked Lean theorems.
See the [data model](data-model.md) for the complete publication policy.

## Setup and checks

Install Bun, Python 3, and elan as linked in the README. Run commands from the
repository root unless a different directory is shown. Keep `bun.lock`,
`formal/lean-toolchain`, and `formal/lake-manifest.json` unchanged when reproducing
a build; `lake update` is for intentional dependency updates, not routine setup.

```console
bun install --frozen-lockfile
bun run archive:build
bun run check
bun run test
bun run build
bun run format:check
(cd formal && lake exe cache get && lake --wfail build)
```

The axiom-policy tests below require the Lean build above. They check that
standard dependencies are accepted and custom axioms, unfinished proofs, and
native-evaluation dependencies are rejected.

```console
python3 -S -m unittest discover -s scripts -p test_lean_evidence_audit.py
python3 -S -m unittest discover -s scripts -p test_lean_axiom_policy.py
bunx playwright install --with-deps chromium
bun run test:e2e
```

The [CI workflow](../.github/workflows/ci.yml) also reproduces geometric covers
and runs the research experiments' checks. See [generated geometric covers](generated-geometric-covers.md)
for their generators and tests.

## Local site and deployment

```console
bun run dev
```

The normal build uses the `/square-packing-archive/` base path. The public site
is deployed to GitHub Pages by the [Pages workflow](../.github/workflows/pages.yml),
called only after the archive/web and Lean CI jobs pass on `main`.

The optional Sites package uses the same app with an origin-root base path:

```console
bun run site:package
```

This produces `dist/site.tar.gz` with the static site and deployment metadata.
The [packaging script](../scripts/package-site.ts) packages this Vite app;
the Worker-only helper and Sites Vite plugin are not used. The social-preview
image and its generation prompt are documented in the [artwork notes](site-artwork.md).

## Coordinates and reproducible imports

Grid layouts and the 5- and 10-square Göbel constructions come from manifest
recipes. Göbel's coordinates retain exact square-root expressions. Every archive
build checks unit frames, containment, and non-overlap with exact arithmetic;
this computational check is separate from the Lean proof. Details are in the
[configuration model](data-model.md#configuration).

The following import example requires the companion research workspace. It is
not needed to build the archive from the checked-in data:

```console
python3 scripts/import-research-records.py \
  ../square-packing-research/records/square-68.json \
  archive/configurations/square-68.json

python3 scripts/generate-lean-certificates.py \
  archive/configurations/square-68.json \
  formal/SquarePackingArchive/Records/Square68.lean
```

The importer replaces floating angles with rational tangent-half-angle values,
so frame coordinates and separating-axis checks use exact rational arithmetic
in Lean. This is a reconstruction, not a claim that the original floating-point
coordinates were exact.

After changing claim or proof metadata, regenerate its typed audit:

```console
python3 scripts/generate-lean-evidence-audit.py
bun run archive:build
```

Then rerun the checks above. Generated files must agree with the canonical data.

## Geometric proof notes

- [Friedman's unavoidable-point method](friedman-unavoidable-formalization.md)
- [Bentz's staggered-lattice method](bentz-lattice-formalization.md)
- [Moving unavoidable configurations](bentz-moving-unavoidable-formalization.md)
- [The 6-, 10-, 13-, 22-, and 33-square results](small-records-formalization.md)
- [Corrections to Bentz's auxiliary sets for 13](bentz-13-formalization.md)
- [Nagamochi's 2005 paper: scope and proof status](nagamochi-2005-formalization.md)

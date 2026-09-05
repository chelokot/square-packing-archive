# Canonical data model

The archive separates mathematical claims from evidence and configurations.

## Claim

A claim is an immutable historical event asserting one relation:

```text
s(n) ≤ value
s(n) ≥ value
s(n) = value
```

Its `active` flag indicates the current curated claim for that `n`; it does not
erase older records. `supersedes` forms an explicit record lineage.

`value.lean` is the exact formal value required by every catalog claim; the decimal is
display data and may be rounded. The evidence generator combines that value
with the claim's `n` and relation to check the complete expected theorem type.
Display expressions and decimal approximations require a separate consistency
review: the typed Lean audit checks `value.lean`, not prose or decimal formatting.

## Evidence

Evidence describes why a claim is present. It never changes the relation itself.
Tracker records, publications, computational certificates, and Lean proofs are
different evidence kinds. Every catalog claim must include its own `lean-proof`
evidence, including inactive historical records. The other evidence kinds retain
source provenance. Results awaiting formalization belong in GitHub issues.
The public matrix uses color for exactness, not evidence status.

Each Lean evidence record requires `checkedAt`, the full calendar date
(`YYYY-MM-DD`) when that theorem was first recorded as checked for this claim.
This date belongs to the evidence, independently of the claim's historical
`announcedAt`. Non-Lean evidence cannot use `checkedAt`.

The initial dates were recovered from the first Git commit introducing each
claim/theorem pair in `archive/manifest.json`, using the commit's recorded author
date. These record when the archive first attested verification, not an earlier
unrecorded local proof run. Existing evidence is dated August 16, 20, or 29, 2026;
future additions must record their own check dates.

The exact-coverage timeline counts distinct `n`, including inactive historical
claims. Publication events use `announcedAt` only for `published-proof` or
`elementary-proof` evidence with `published` status. Lean verification events use
their own `checkedAt`. The timeline includes years from both event sets, so a
modern formalization never appears verified in the original publication year.
Repeated proofs of the same `n` do not increase either cumulative count. Tracker
reports alone do not count as published proofs.

Historical provenance and present-day verification remain separate. A later,
stronger kernel-checked packing may prove an older upper-bound claim without
being attributed to the historical discoverer or presented as a reconstruction
of the original coordinates. The original tracker or publication evidence stays
on the claim, while the later Lean evidence names the theorem that now proves
the same mathematical inequality.

## Configuration

A configuration stores unit-square centers in physical Cartesian coordinates.
Imported rational configurations represent orientations by an exact rational tangent-half-angle `t`:

```text
cos θ = (1 - t²) / (1 + t²)
sin θ = 2t / (1 + t²)
```

This makes orthonormality an algebraic identity and every containment and
separating-axis comparison rational. Decimal angles exist only as display data.

The manifest can reference a coordinate file or an exact construction recipe.
`grid` stores only the square count and integer container side; its column-major
ordering matches Lean's `SquareNumbers.gridPacking`. `goebel` reconstructs the
5- or 10-square layout from the corresponding Lean construction. No duplicate
coordinate files are needed. Generated layouts support the same viewer,
inspection, and JSON download as imported layouts.

Göbel's coordinates use numbers in `Q(√2)`, encoded as
`{ rational: Ratio, sqrtTwo: Ratio }`, meaning `rational + sqrtTwo × √2`.
They are not rounded to rational numbers. The viewer converts them to floating
point only for drawing and approximate decimal labels; exact inspection and
downloads retain the expressions.

Every archive build independently checks unit frames, tangent reconstruction,
containment, and all pairwise separating axes with exact integer arithmetic in
`Q(√2)`. This computational check does not create Lean evidence. Grid recipe
instances also receive typed Lean upper-bound checks, while the 5- and 10-square
constructions have their own explicit Lean packings. Lower bounds enter the
catalog only after their own Lean proofs are complete.

For an uncatalogued count, the manifest's `gridBaseline` policy supplies a
Lean-checked upper bound and generated grid coordinates. These appear as white
cells in the matrix. They are not historical records and do not contribute to
catalogue totals or the exact-result timeline.

## Generated consumers

The TypeScript domain package validates references and derives dashboard views.
The web build receives one compiled JSON artifact. The Lean generator emits
record-specific certificate modules. A second generator emits a typed `example`
for every `lean-proof` theorem named by the manifest, so CI rejects stale names
and theorems whose `n`, relation, or exact value differs from the claim. CI fails
if any consumer disagrees with the canonical archive. Each linked theorem's
transitive axiom dependencies must be contained in `propext`, `Classical.choice`,
and `Quot.sound`; custom axioms, unfinished proofs, and native-evaluation oracles
are rejected. GitHub Pages deployment waits for both archive/web and Lean CI.

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

`value.lean` is the exact formal value used by verified claims; the decimal is
display data and may be rounded. The evidence generator combines that value
with the claim's `n` and relation to check the complete expected theorem type.

## Evidence

Evidence describes why a claim is present. It never changes the relation itself.
Tracker records, publications, computational certificates, and Lean proofs are
different evidence kinds. Derived verification status is a pure function of this
evidence, with `lean-proof` as the only verified state.

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
Every orientation is represented by an exact rational tangent-half-angle `t`:

```text
cos θ = (1 - t²) / (1 + t²)
sin θ = 2t / (1 + t²)
```

This makes orthonormality an algebraic identity and every containment and
separating-axis comparison rational. Decimal angles exist only as display data.

## Generated consumers

The TypeScript domain package validates references and derives dashboard views.
The web build receives one compiled JSON artifact. The Lean generator emits
record-specific certificate modules. A second generator emits a typed `example`
for every `lean-proof` theorem named by the manifest, so CI rejects stale names
and theorems whose `n`, relation, or exact value differs from the claim. CI fails
if any consumer disagrees with the canonical archive.

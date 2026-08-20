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

## Evidence

Evidence describes why a claim is present. It never changes the relation itself.
Tracker records, publications, computational certificates, and Lean proofs are
different evidence kinds. Derived verification status is a pure function of this
evidence, with `lean-proof` as the only verified state.

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
record-specific certificate modules. CI fails if either consumer disagrees with
the canonical archive.

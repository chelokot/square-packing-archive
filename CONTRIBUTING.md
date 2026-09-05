# Contributing

Contributions are welcome: new packings, stronger lower bounds, historical
corrections, primary sources, exact reconstructions, Lean formalizations, viewer
features, and independent reviews all belong here.

The published catalog contains only Lean-checked mathematical results, including
inactive historical records. Open an issue for a proposal that is not yet
formalized. Keep its sources, coordinates, discovery dates, and attribution in
the issue so they can accompany a later verified submission.

## Submission classes

### New or improved upper bound

To add a result to the catalog, submit:

1. a new immutable claim in `archive/manifest.json`;
2. author roles and primary-source links;
3. a configuration in the physical bottom-left coordinate system;
4. an exact rational certificate or enough precision to reproduce one;
5. a Lean module and the exact theorem name proving `HasPacking n side` for the
   recorded bound;
6. passing CI, including the generated manifest theorem checks and `lake build`.

The new claim must point to the previous record with `supersedes`. Old records
remain in the archive and become inactive; record history is never overwritten.

### Lower bound or exact result

Include primary sources and a linked Lean theorem proving the recorded
`IsLowerBound n side` or `IsMinimumSide n side`. An exact result needs both
directions of the equality. The theorem must pass the manifest's typed checks
and CI before the claim enters the catalog. Published proofs awaiting
formalization belong in issues, not in active or inactive catalog entries.

### Historical correction

Prefer primary sources. Explain the discrepancy, preserve the earlier archive
state in Git history, and distinguish discoverer, optimizer, and prover roles.
Metadata and attribution corrections do not need a new mathematical proof.
Changing the bound or relation does: link the theorem for the corrected claim.

## Verification policy

Every catalog claim must have its own `lean-proof` evidence with status
`lean-checked`, a local Lean artifact, a fully qualified theorem name, and a
verification date. The claim must include its exact Lean value. Archive
validation and the generated Lean audit enforce this for all records; marking
a claim inactive does not waive the requirement. CI checks the linked theorem
against the claim's count, bound, and relation, not just its metadata.

Lean files must contain no `sorry`, custom axioms, or unchecked foreign proof
oracle. The generated audit checks the transitive dependencies of every linked
theorem, including grid baselines. It rejects any axiom except `propext`,
`Classical.choice`, and `Quot.sound`; native-evaluation oracles are rejected too.
`#print axioms` remains available for inspecting those dependencies.

Computational search code may be untrusted. A certificate becomes verified only
when a small proved checker consumes exact data and Lean's kernel accepts the
resulting theorem.

## Pull request checklist

- Preserve immutable claim identifiers and provenance.
- Add every author and source reference to the manifest.
- Run `bun run archive:build`, `bun run check`, `bun run test`, and
  `bun run build`.
- For mathematical result additions or changes, link the exact Lean theorem
  and passing CI; run `lake build` in `formal`.
- Confirm generated files are current.
- Describe numerical tolerances and reconstruction choices honestly.
- Keep unformalized proposals in issues, with their sources and attribution.

UI, documentation, and other non-mathematical changes do not require a Lean
proof. Run the checks relevant to those changes.

By contributing code or Lean sources, you agree to Apache-2.0. By contributing
archive metadata or original visualizations, you agree to CC BY 4.0.

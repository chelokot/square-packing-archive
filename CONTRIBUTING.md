# Contributing

Contributions are welcome: new packings, stronger lower bounds, historical
corrections, primary sources, exact reconstructions, Lean formalizations, viewer
features, and independent reviews all belong here.

## Submission classes

### New or improved upper bound

Submit:

1. a new immutable claim in `archive/manifest.json`;
2. author roles and primary-source links;
3. a configuration in the physical bottom-left coordinate system;
4. an exact rational certificate or enough precision to reproduce one;
5. a generated Lean module when claiming verified status.

The new claim must point to the previous record with `supersedes`. Old records
remain in the archive and become inactive; record history is never overwritten.

### Lower bound or exact result

Submit the bibliographic claim first, then the Lean theorem and its dependency
path. A publication alone receives `published · awaiting Lean`. An exact result
receives `Lean verified` only when both directions of the claimed equality are
formalized.

### Historical correction

Prefer primary sources. Explain the discrepancy, preserve the earlier archive
state in Git history, and distinguish discoverer, optimizer, and prover roles.

## Verification policy

The string `lean-checked` is accepted only for `lean-proof` evidence. Archive
validation rejects any other use. Lean files must contain no `sorry`, custom
axioms, or unchecked foreign proof oracle. Standard Mathlib axioms such as
classical choice are reported normally by `#print axioms` and are not hidden.

Computational search code may be untrusted. A certificate becomes verified only
when a small proved checker consumes exact data and Lean's kernel accepts the
resulting theorem.

## Pull request checklist

- Preserve immutable claim identifiers and provenance.
- Add every author and source reference to the manifest.
- Run `bun run archive:build`, `bun run check`, `bun run test`, and
  `bun run build`.
- Run `lake build` in `formal` for proof changes.
- Confirm generated files are current.
- Describe numerical tolerances and reconstruction choices honestly.
- Never label a result verified without a linked Lean theorem.

By contributing code or Lean sources, you agree to Apache-2.0. By contributing
archive metadata or original visualizations, you agree to CC BY 4.0.

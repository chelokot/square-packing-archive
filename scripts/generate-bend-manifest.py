#!/usr/bin/env python3
"""Write bend/MANIFEST.bend: a law for each claim with a Bend proof, stated from archive/manifest.json.

The grid baseline is a packing of any n <= k^2 squares in side k. An upper
bound s(n) <= v is a packing of n squares in side v. A lower bound
v <= s(n) holds for every packing of at least n squares. A value written with
`root` is stated for every root >= 0 of root * root = 2. bend/PROOF.bend fills
each law, so `bend bend/PROOF.bend --verdict` checks every claim as the
catalog states it.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent

HEADER = '''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
'''


def law_name(claim, bound):
    return claim['id'].replace('-', '_') + '_' + bound


ROOT_BINDER = '''
  for ~root: F'''
ROOT_FACTS = '''
  for +root_below: A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, root, root), R.FieldRing.of_nat(~F, ~field, 2n))
  for +root_above: A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, 2n), A.Algebra.mul(~F, ~field, root, root))
  for +root_sign: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), root)'''


def laws(claim):
    """The laws of a claim; a value with `root` holds for every square root of 2 in the field."""
    n, value = claim['n'], claim['value']['bend']
    binder, facts = (ROOT_BINDER, ROOT_FACTS) if 'root' in value else ('', '')
    if claim['relation'] in ('exact', 'upper'):
        yield f'''
law {law_name(claim, 'upper')}:
  for ~F: Kind(&2)
  for ~field: K.Field<F>{binder}{facts}
  P.Problem.Packing<F, field, {n}n, {value}>
'''
    if claim['relation'] in ('exact', 'lower'):
        yield f'''
law {law_name(claim, 'lower')}:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>{binder}{facts}
  for +at_least: N.Natural.Le({n}n, count)
  A.Algebra.le(~F, ~field, {value}, side)
'''


GRID_BASELINE = '''
law grid_baseline:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~size: Nat
  for ~count: Nat
  for +fits: N.Natural.Le(count, Nat.mul(1n+size, 1n+size))
  P.Problem.Packing<F, field, count, R.FieldRing.of_nat(~F, ~field, 1n+size)>
'''


def main():
    manifest = json.loads((ROOT / 'archive' / 'manifest.json').read_text())
    parts = [HEADER] + ([GRID_BASELINE] if 'gridBaseline' in manifest else [])
    for claim in manifest['claims']:
        if any(proof['kind'] == 'bend-proof' for proof in claim['evidence']):
            parts.extend(laws(claim))
    (ROOT / 'bend' / 'MANIFEST.bend').write_text(''.join(parts))


if __name__ == '__main__':
    main()

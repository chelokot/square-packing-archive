#!/usr/bin/env python3
"""Write bend/MANIFEST.bend: a law for each claim with a Bend proof, stated from archive/manifest.json.

The grid baseline is a packing of any n <= k^2 squares in side k. An upper
bound s(n) <= v is a packing of n squares in side v. A lower bound
v <= s(n) holds for every packing of at least n squares. bend/PROOF.bend fills
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


def laws(claim):
    n, value = claim['n'], claim['value']['bend']
    if claim['relation'] in ('exact', 'upper'):
        yield f'''
law {law_name(claim, 'upper')}:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  P.Problem.Packing<F, field, {n}n, {value}>
'''
    if claim['relation'] in ('exact', 'lower'):
        yield f'''
law {law_name(claim, 'lower')}:
  for ~F: Kind(&2)
  for ~field: K.Field<F>
  for ~count: Nat
  for ~side: F
  for ~packing: P.Problem.Packing<F, field, count, side>
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

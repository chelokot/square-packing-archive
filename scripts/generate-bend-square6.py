#!/usr/bin/env python3
"""Write bend/Square6.bend: six unit squares in a 3 by 2 grid inside side 3.

The grid geometry lives in bend/Grid.bend; this script only enumerates the six
cells and the 36 ordered pairs of cell indices.
"""
import pathlib
import re

def expand(src, pre='A.Algebra.'):
  rep=[('TPL','~F: Kind(&2), ~field: K.Field<F>'),('TC','~F, ~field'),
    ('ZERO',pre+'zero(~F, ~field)'),('ONE',pre+'one(~F, ~field)'),('HALF',pre+'half(~F, ~field)')]
  for a,b in rep:
    src=re.sub(r'\b%s\b'%a,b,src)
  for op,name in [('ADD','add'),('NEG','neg'),('MUL','mul'),('LE','le'),('SAME','Same')]:
    src=re.sub(r'\b%s\('%op,pre+'%s(~F, ~field, '%name,src)
  return src
cells=[(i%3,i//3) for i in range(6)]
def nest(var, depth, leaf, default, ind):
  out=[]
  def go(k, v, ind):
    if k==depth:
      out.append(' '*ind+default(v)); return
    out.append(' '*ind+f'match {v}:')
    out.append(' '*(ind+2)+'case 0n:')
    out.append(' '*(ind+4)+leaf(k))
    nv=f'{var}_{k+1}'
    out.append(' '*(ind+2)+f'case 1n+{nv}:')
    go(k+1, nv, ind+4)
  go(0, var, ind); return '\n'.join(out)
L=[]
L.append('''import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Grid.bend as Q
''')
for name,ix in [('column',0),('row',1)]:
  L.append(f'def Square6.{name}(index: Nat) -> Nat:\n'+nest('index',6,lambda k:f'{cells[k][ix]}n',lambda v:'0n',2)+'\n')
  L.append(f'def Square6.{name}_small(index: Nat) -> N.Natural.Le(Square6.{name}(index), 2n):\n'+nest('index',6,lambda k:'Unit{}',lambda v:'Unit{}',2)+'\n')
L.append('''def Square6.square(TPL, +index: Nat) -> P.Problem.Square<F, field>:
  Q.Grid.cell(TC, Square6.column(index), Square6.row(index))

def Square6.fits(TPL, +index: Nat, bound: N.Natural.Le(1n+index, 6n), +point: P.Problem.Point<F>,
  containment: P.Problem.Containment<F, field, Square6.square(TC, index), point>) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(TC, 3n), point>:
  Q.Grid.fits(TC, Square6.column(index), Square6.row(index), Square6.column_small(index), Square6.row_small(index), point, containment)
''')
def coord(n): return f'ADD(HALF, R.FieldRing.of_nat(TC, {n}n))'
def leaf_pair(i,j):
  if i==j: return 'different({==})'
  (ci,ri),(cj,rj)=cells[i],cells[j]
  if ci!=cj:
    a,b,first,second=(i,j,'first','second') if ci<cj else (j,i,'second','first')
    (ca,ra),(cb,rb)=cells[a],cells[b]
    return f'Q.Grid.separated_x(TC, {coord(ca)}, {coord(ra)}, {coord(cb)}, {coord(rb)}, Q.Grid.offset_gap(TC, {ca}n, {cb}n, Unit{{}}), point, {first}, {second})'
  a,b,first,second=(i,j,'first','second') if ri<rj else (j,i,'second','first')
  (ca,ra),(cb,rb)=cells[a],cells[b]
  return f'Q.Grid.separated_y(TC, {coord(ca)}, {coord(ra)}, {coord(cb)}, {coord(rb)}, Q.Grid.offset_gap(TC, {ra}n, {rb}n, Unit{{}}), point, {first}, {second})'
lines=[]
def go_left(k, v, ind):
  if k==6:
    lines.append(' '*ind+'left_bound'); return
  lines.append(' '*ind+f'match {v}:')
  lines.append(' '*(ind+2)+'case 0n:')
  go_right(k, 0, 'right', ind+4)
  nv=f'left_{k+1}'
  lines.append(' '*(ind+2)+f'case 1n+{nv}:')
  go_left(k+1, nv, ind+4)
def go_right(i, k, v, ind):
  if k==6:
    lines.append(' '*ind+'right_bound'); return
  lines.append(' '*ind+f'match {v}:')
  lines.append(' '*(ind+2)+'case 0n:')
  lines.append(' '*(ind+4)+leaf_pair(i,k))
  nv=f'right_{k+1}'
  lines.append(' '*(ind+2)+f'case 1n+{nv}:')
  go_right(i, k+1, nv, ind+4)
go_left(0,'left',2)
L.append('''def Square6.disjoint(TPL, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, 6n), right_bound: N.Natural.Le(1n+right, 6n),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Square6.square(TC, left), point>,
  second: P.Problem.InteriorContainment<F, field, Square6.square(TC, right), point>) -> Empty:
'''+'\n'.join(lines)+'\n')
L.append('''def Square6.packing(TPL) -> P.Problem.Packing<F, field, 6n, R.FieldRing.of_nat(TC, 3n)>:
  P.Packing{
    index => Square6.square(TC, index),
    O.FieldOrder.zero_le_of_nat(TC, 3n),
    index => bound => point => containment => Square6.fits(TC, index, bound, point, containment),
    left => right => left_bound => right_bound => different => point => first => second =>
      Square6.disjoint(TC, left, right, left_bound, right_bound, different, point, first, second)
  }
''')
source='\n'.join(L)

target=pathlib.Path(__file__).resolve().parent.parent/'bend'/'Square6.bend'
target.write_text(expand(source))

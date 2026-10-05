import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Grid.bend as Q

def Square1.column(index: Nat) -> Nat:
  match index:
    case 0n:
      0n
    case 1n+index_1:
      0n

def Square1.column_small(index: Nat) -> N.Natural.Le(Square1.column(index), 0n):
  match index:
    case 0n:
      Unit{}
    case 1n+index_1:
      Unit{}

def Square1.row(index: Nat) -> Nat:
  match index:
    case 0n:
      0n
    case 1n+index_1:
      0n

def Square1.row_small(index: Nat) -> N.Natural.Le(Square1.row(index), 0n):
  match index:
    case 0n:
      Unit{}
    case 1n+index_1:
      Unit{}

def Square1.square(~F: Kind(&2), ~field: K.Field<F>, +index: Nat) -> P.Problem.Square<F, field>:
  Q.Grid.cell(~F, ~field, Square1.column(index), Square1.row(index))

def Square1.fits(~F: Kind(&2), ~field: K.Field<F>, +index: Nat, bound: N.Natural.Le(1n+index, 1n), +point: P.Problem.Point<F>,
  containment: P.Problem.Containment<F, field, Square1.square(~F, ~field, index), point>) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(~F, ~field, 1n), point>:
  Q.Grid.fits(~F, ~field, 0n, Square1.column(index), Square1.row(index), Square1.column_small(index), Square1.row_small(index), point, containment)

def Square1.disjoint(~F: Kind(&2), ~field: K.Field<F>, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, 1n), right_bound: N.Natural.Le(1n+right, 1n),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Square1.square(~F, ~field, left), point>,
  second: P.Problem.InteriorContainment<F, field, Square1.square(~F, ~field, right), point>) -> Empty:
  match left:
    case 0n:
      match right:
        case 0n:
          different({==})
        case 1n+right_1:
          right_bound
    case 1n+left_1:
      left_bound

def Square1.packing(~F: Kind(&2), ~field: K.Field<F>) -> P.Problem.Packing<F, field, 1n, R.FieldRing.of_nat(~F, ~field, 1n)>:
  P.Packing{
    index => Square1.square(~F, ~field, index),
    O.FieldOrder.zero_le_of_nat(~F, ~field, 1n),
    index => bound => point => containment => Square1.fits(~F, ~field, index, bound, point, containment),
    left => right => left_bound => right_bound => different => point => first => second =>
      Square1.disjoint(~F, ~field, left, right, left_bound, right_bound, different, point, first, second)
  }

import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Grid.bend as Q

def Square4.column(index: Nat) -> Nat:
  match index:
    case 0n:
      0n
    case 1n+index_1:
      match index_1:
        case 0n:
          1n
        case 1n+index_2:
          match index_2:
            case 0n:
              0n
            case 1n+index_3:
              match index_3:
                case 0n:
                  1n
                case 1n+index_4:
                  0n

def Square4.column_small(index: Nat) -> N.Natural.Le(Square4.column(index), 1n):
  match index:
    case 0n:
      Unit{}
    case 1n+index_1:
      match index_1:
        case 0n:
          Unit{}
        case 1n+index_2:
          match index_2:
            case 0n:
              Unit{}
            case 1n+index_3:
              match index_3:
                case 0n:
                  Unit{}
                case 1n+index_4:
                  Unit{}

def Square4.row(index: Nat) -> Nat:
  match index:
    case 0n:
      0n
    case 1n+index_1:
      match index_1:
        case 0n:
          0n
        case 1n+index_2:
          match index_2:
            case 0n:
              1n
            case 1n+index_3:
              match index_3:
                case 0n:
                  1n
                case 1n+index_4:
                  0n

def Square4.row_small(index: Nat) -> N.Natural.Le(Square4.row(index), 1n):
  match index:
    case 0n:
      Unit{}
    case 1n+index_1:
      match index_1:
        case 0n:
          Unit{}
        case 1n+index_2:
          match index_2:
            case 0n:
              Unit{}
            case 1n+index_3:
              match index_3:
                case 0n:
                  Unit{}
                case 1n+index_4:
                  Unit{}

def Square4.square(~F: Kind(&2), ~field: K.Field<F>, +index: Nat) -> P.Problem.Square<F, field>:
  Q.Grid.cell(~F, ~field, Square4.column(index), Square4.row(index))

def Square4.fits(~F: Kind(&2), ~field: K.Field<F>, +index: Nat, bound: N.Natural.Le(1n+index, 4n), +point: P.Problem.Point<F>,
  containment: P.Problem.Containment<F, field, Square4.square(~F, ~field, index), point>) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(~F, ~field, 2n), point>:
  Q.Grid.fits(~F, ~field, 1n, Square4.column(index), Square4.row(index), Square4.column_small(index), Square4.row_small(index), point, containment)

def Square4.disjoint(~F: Kind(&2), ~field: K.Field<F>, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, 4n), right_bound: N.Natural.Le(1n+right, 4n),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Square4.square(~F, ~field, left), point>,
  second: P.Problem.InteriorContainment<F, field, Square4.square(~F, ~field, right), point>) -> Empty:
  match left:
    case 0n:
      match right:
        case 0n:
          different({==})
        case 1n+right_1:
          match right_1:
            case 0n:
              Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
            case 1n+right_2:
              match right_2:
                case 0n:
                  Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
                case 1n+right_3:
                  match right_3:
                    case 0n:
                      Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
                    case 1n+right_4:
                      right_bound
    case 1n+left_1:
      match left_1:
        case 0n:
          match right:
            case 0n:
              Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
            case 1n+right_1:
              match right_1:
                case 0n:
                  different({==})
                case 1n+right_2:
                  match right_2:
                    case 0n:
                      Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
                    case 1n+right_3:
                      match right_3:
                        case 0n:
                          Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
                        case 1n+right_4:
                          right_bound
        case 1n+left_2:
          match left_2:
            case 0n:
              match right:
                case 0n:
                  Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
                case 1n+right_1:
                  match right_1:
                    case 0n:
                      Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
                    case 1n+right_2:
                      match right_2:
                        case 0n:
                          different({==})
                        case 1n+right_3:
                          match right_3:
                            case 0n:
                              Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, first, second)
                            case 1n+right_4:
                              right_bound
            case 1n+left_3:
              match left_3:
                case 0n:
                  match right:
                    case 0n:
                      Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
                    case 1n+right_1:
                      match right_1:
                        case 0n:
                          Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
                        case 1n+right_2:
                          match right_2:
                            case 0n:
                              Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 0n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, 1n)), Q.Grid.offset_gap(~F, ~field, 0n, 1n, Unit{}), point, second, first)
                            case 1n+right_3:
                              match right_3:
                                case 0n:
                                  different({==})
                                case 1n+right_4:
                                  right_bound
                case 1n+left_4:
                  left_bound

def Square4.packing(~F: Kind(&2), ~field: K.Field<F>) -> P.Problem.Packing<F, field, 4n, R.FieldRing.of_nat(~F, ~field, 2n)>:
  P.Packing{
    index => Square4.square(~F, ~field, index),
    O.FieldOrder.zero_le_of_nat(~F, ~field, 2n),
    index => bound => point => containment => Square4.fits(~F, ~field, index, bound, point, containment),
    left => right => left_bound => right_bound => different => point => first => second =>
      Square4.disjoint(~F, ~field, left, right, left_bound, right_bound, different, point, first, second)
  }

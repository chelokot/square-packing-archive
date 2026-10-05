import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Symmetry.bend as Y

def Packings.squares(-F: Kind(&2), -field: K.Field<F>, -count: Nat, -side: F, packing: P.Problem.Packing<F, field, count, side>) ->
  Nat -> P.Problem.Square<F, field>:
  match packing:
    case P.Packing{squares, side_nonnegative, fits, disjoint}:
      squares

def Packings.side_nonnegative(-F: Kind(&2), -field: K.Field<F>, -count: Nat, -side: F, packing: P.Problem.Packing<F, field, count, side>) ->
  K.Field.le(F, field)(K.Field.zero(F, field), side):
  match packing:
    case P.Packing{squares, side_nonnegative, fits, disjoint}:
      side_nonnegative

def Packings.fits(-F: Kind(&2), -field: K.Field<F>, -count: Nat, -side: F, packing: P.Problem.Packing<F, field, count, side>) ->
  @index: Nat -> N.Natural.Le(1n+index, count) -> @point: P.Problem.Point<F> ->
    P.Problem.Containment<F, field, Packings.squares(F, field, count, side, packing)(index), point> -> P.Problem.InContainer<F, field, side, point>:
  match packing:
    case P.Packing{squares, side_nonnegative, fits, disjoint}:
      fits

def Packings.disjoint(-F: Kind(&2), -field: K.Field<F>, -count: Nat, -side: F, packing: P.Problem.Packing<F, field, count, side>) ->
  @left: Nat -> @right: Nat -> N.Natural.Le(1n+left, count) -> N.Natural.Le(1n+right, count) ->
    ({left == right : Nat} -> Empty) -> @point: P.Problem.Point<F> ->
    P.Problem.InteriorContainment<F, field, Packings.squares(F, field, count, side, packing)(left), point> ->
    P.Problem.InteriorContainment<F, field, Packings.squares(F, field, count, side, packing)(right), point> -> Empty:
  match packing:
    case P.Packing{squares, side_nonnegative, fits, disjoint}:
      disjoint

def Packings.swap_square(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat) -> P.Problem.Square<F, field>:
  Y.Symmetry.swap(~F, ~field, Packings.squares(F, field, count, side, packing)(index))

def Packings.swap_fits(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat, bound: N.Natural.Le(1n+index, count)) ->
  Y.Symmetry.Fits(~F, ~field, Packings.swap_square(~F, ~field, ~count, ~side, ~packing, index), side):
  Y.Symmetry.swap_fits(~F, ~field, Packings.squares(F, field, count, side, packing)(index), side, Packings.fits(F, field, count, side, packing)(index, bound))

def Packings.swap_disjoint(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, count), right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Packings.swap_square(~F, ~field, ~count, ~side, ~packing, left), point>,
  second: P.Problem.InteriorContainment<F, field, Packings.swap_square(~F, ~field, ~count, ~side, ~packing, right), point>) -> Empty:
  Packings.disjoint(F, field, count, side, packing)(left, right, left_bound, right_bound, different, Y.Symmetry.swap_point(F, point),
    Y.Symmetry.swap_interior_back(~F, ~field, Packings.squares(F, field, count, side, packing)(left), point, first),
    Y.Symmetry.swap_interior_back(~F, ~field, Packings.squares(F, field, count, side, packing)(right), point, second))

def Packings.swap(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>) -> P.Problem.Packing<F, field, count, side>:
  P.Packing{
    index => Packings.swap_square(~F, ~field, ~count, ~side, ~packing, index),
    Packings.side_nonnegative(F, field, count, side, packing),
    index => bound => Packings.swap_fits(~F, ~field, ~count, ~side, ~packing, index, bound),
    left => right => left_bound => right_bound => different => point => first => second =>
      Packings.swap_disjoint(~F, ~field, ~count, ~side, ~packing, left, right, left_bound, right_bound, different, point, first, second)
  }

def Packings.reflect_x_square(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat) -> P.Problem.Square<F, field>:
  Y.Symmetry.reflect_x(~F, ~field, side, Packings.squares(F, field, count, side, packing)(index))

def Packings.reflect_x_fits(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat, bound: N.Natural.Le(1n+index, count)) ->
  Y.Symmetry.Fits(~F, ~field, Packings.reflect_x_square(~F, ~field, ~count, ~side, ~packing, index), side):
  Y.Symmetry.reflect_x_fits(~F, ~field, Packings.squares(F, field, count, side, packing)(index), side, Packings.fits(F, field, count, side, packing)(index, bound))

def Packings.reflect_x_disjoint(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, count), right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Packings.reflect_x_square(~F, ~field, ~count, ~side, ~packing, left), point>,
  second: P.Problem.InteriorContainment<F, field, Packings.reflect_x_square(~F, ~field, ~count, ~side, ~packing, right), point>) -> Empty:
  Packings.disjoint(F, field, count, side, packing)(left, right, left_bound, right_bound, different, Y.Symmetry.reflect_x_point(~F, ~field, side, point),
    Y.Symmetry.reflect_x_interior_back(~F, ~field, side, Packings.squares(F, field, count, side, packing)(left), point, first),
    Y.Symmetry.reflect_x_interior_back(~F, ~field, side, Packings.squares(F, field, count, side, packing)(right), point, second))

def Packings.reflect_x(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>) -> P.Problem.Packing<F, field, count, side>:
  P.Packing{
    index => Packings.reflect_x_square(~F, ~field, ~count, ~side, ~packing, index),
    Packings.side_nonnegative(F, field, count, side, packing),
    index => bound => Packings.reflect_x_fits(~F, ~field, ~count, ~side, ~packing, index, bound),
    left => right => left_bound => right_bound => different => point => first => second =>
      Packings.reflect_x_disjoint(~F, ~field, ~count, ~side, ~packing, left, right, left_bound, right_bound, different, point, first, second)
  }

def Packings.reflect_y_square(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat) -> P.Problem.Square<F, field>:
  Y.Symmetry.reflect_y(~F, ~field, side, Packings.squares(F, field, count, side, packing)(index))

def Packings.reflect_y_fits(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +index: Nat, bound: N.Natural.Le(1n+index, count)) ->
  Y.Symmetry.Fits(~F, ~field, Packings.reflect_y_square(~F, ~field, ~count, ~side, ~packing, index), side):
  Y.Symmetry.reflect_y_fits(~F, ~field, Packings.squares(F, field, count, side, packing)(index), side, Packings.fits(F, field, count, side, packing)(index, bound))

def Packings.reflect_y_disjoint(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, +left: Nat, +right: Nat,
  left_bound: N.Natural.Le(1n+left, count), right_bound: N.Natural.Le(1n+right, count),
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Packings.reflect_y_square(~F, ~field, ~count, ~side, ~packing, left), point>,
  second: P.Problem.InteriorContainment<F, field, Packings.reflect_y_square(~F, ~field, ~count, ~side, ~packing, right), point>) -> Empty:
  Packings.disjoint(F, field, count, side, packing)(left, right, left_bound, right_bound, different, Y.Symmetry.reflect_y_point(~F, ~field, side, point),
    Y.Symmetry.reflect_y_interior_back(~F, ~field, side, Packings.squares(F, field, count, side, packing)(left), point, first),
    Y.Symmetry.reflect_y_interior_back(~F, ~field, side, Packings.squares(F, field, count, side, packing)(right), point, second))

def Packings.reflect_y(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>) -> P.Problem.Packing<F, field, count, side>:
  P.Packing{
    index => Packings.reflect_y_square(~F, ~field, ~count, ~side, ~packing, index),
    Packings.side_nonnegative(F, field, count, side, packing),
    index => bound => Packings.reflect_y_fits(~F, ~field, ~count, ~side, ~packing, index, bound),
    left => right => left_bound => right_bound => different => point => first => second =>
      Packings.reflect_y_disjoint(~F, ~field, ~count, ~side, ~packing, left, right, left_bound, right_bound, different, point, first, second)
  }


def Packings.restrict(~F: Kind(&2), ~field: K.Field<F>, ~count: Nat, ~side: F, ~packing: P.Problem.Packing<F, field, count, side>, ~fewer: Nat,
  +at_most: N.Natural.Le(fewer, count)) -> P.Problem.Packing<F, field, fewer, side>:
  P.Packing{
    Packings.squares(F, field, count, side, packing),
    Packings.side_nonnegative(F, field, count, side, packing),
    +index => bound => Packings.fits(F, field, count, side, packing)(index, N.Natural.le_transitive(1n+index, fewer, count, bound, at_most)),
    +left => +right => left_bound => right_bound =>
      Packings.disjoint(F, field, count, side, packing)(left, right, N.Natural.le_transitive(1n+left, fewer, count, left_bound, at_most),
        N.Natural.le_transitive(1n+right, fewer, count, right_bound, at_most))
  }

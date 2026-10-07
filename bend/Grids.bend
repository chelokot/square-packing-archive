import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Natural.bend as N
import ./Problem.bend as P
import ./Grid.bend as Q

type Grids.Place<-size: Nat, -index: Nat> is Data:
  Place{quotient: Nat, remainder: Nat, small: N.Natural.Le(remainder, size), spec: {Nat.add(Nat.mul(quotient, 1n+size), remainder) == index : Nat}}

def Grids.successor_le(a: Nat, b: Nat, above: N.Natural.Le(b, a) -> Empty) -> N.Natural.Le(1n+a, b):
  match a b:
    case 0n 0n:
      Empty.absurd(N.Natural.Le(1n, 0n), above(Unit{}))
    case 0n 1n+bp:
      N.Natural.zero_le(bp)
    case 1n+ap 0n:
      above(Unit{})
    case 1n+ap 1n+bp:
      Grids.successor_le(ap, bp, above)

def Grids.le_by(+a: Nat, +b: Nat, decision: Or(N.Natural.Le(b, a), N.Natural.Le(b, a) -> Empty), below: N.Natural.Le(1n+a, b) -> Empty) -> N.Natural.Le(b, a):
  match decision:
    case Inl{le}:
      le
    case Inr{above}:
      Empty.absurd(N.Natural.Le(b, a), below(Grids.successor_le(a, b, above)))

def Grids.le_of_not_successor_le(+a: Nat, +b: Nat, below: N.Natural.Le(1n+a, b) -> Empty) -> N.Natural.Le(b, a):
  Grids.le_by(a, b, N.Natural.le_decidable(b, a), below)

def Grids.advance(+size: Nat, +index: Nat, +quotient: Nat, +remainder: Nat, small: N.Natural.Le(remainder, size),
  spec: {Nat.add(Nat.mul(quotient, 1n+size), remainder) == index : Nat},
  decision: Or(N.Natural.Le(1n+remainder, size), N.Natural.Le(1n+remainder, size) -> Empty)) -> Grids.Place<size, 1n+index>:
  match decision:
    case Inl{room}:
      +before: Nat = Nat.mul(quotient, 1n+size)
      Place{quotient, 1n+remainder, room,
        Equal.trans(Nat, Nat.add(before, 1n+remainder), 1n+Nat.add(before, remainder), 1n+index,
          N.Natural.add_successor(before, remainder),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(before, remainder), index, spec))}
    case Inr{full}:
      +before: Nat = Nat.mul(quotient, 1n+size)
      +last: {remainder == size : Nat} = N.Natural.le_antisymmetric(remainder, size, small, Grids.le_of_not_successor_le(remainder, size, full))
      Place{1n+quotient, 0n, N.Natural.zero_le(size),
        Equal.trans(Nat, Nat.add(1n+Nat.add(size, before), 0n), 1n+Nat.add(size, before), 1n+index,
          N.Natural.add_zero(1n+Nat.add(size, before)),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(size, before), index,
            Equal.trans(Nat, Nat.add(size, before), Nat.add(before, size), index, N.Natural.add_commutative(size, before),
              Equal.trans(Nat, Nat.add(before, size), Nat.add(before, remainder), index,
                Equal.cong(Nat, Nat, z => Nat.add(before, z), size, remainder, Equal.sym(Nat, remainder, size, last)), spec))))}

def Grids.step(+size: Nat, +index: Nat, place: Grids.Place<size, index>) -> Grids.Place<size, 1n+index>:
  match place:
    case Place{+quotient, +remainder, small, spec}:
      Grids.advance(size, index, quotient, remainder, small, spec, N.Natural.le_decidable(1n+remainder, size))

def Grids.place(+size: Nat, index: Nat) -> Grids.Place<size, index>:
  match index:
    case 0n:
      Place{0n, 0n, N.Natural.zero_le(size), {==}}
    case 1n++previous:
      Grids.step(size, previous, Grids.place(size, previous))

def Grids.quotient(-size: Nat, -index: Nat, place: Grids.Place<size, index>) -> Nat:
  match place:
    case Place{quotient, remainder, small, spec}:
      quotient

def Grids.remainder(-size: Nat, -index: Nat, place: Grids.Place<size, index>) -> Nat:
  match place:
    case Place{quotient, remainder, small, spec}:
      remainder

def Grids.remainder_small(-size: Nat, -index: Nat, place: Grids.Place<size, index>) -> N.Natural.Le(Grids.remainder(size, index, place), size):
  match place:
    case Place{quotient, remainder, small, spec}:
      small

def Grids.spec(-size: Nat, -index: Nat, place: Grids.Place<size, index>) ->
  {Nat.add(Nat.mul(Grids.quotient(size, index, place), 1n+size), Grids.remainder(size, index, place)) == index : Nat}:
  match place:
    case Place{quotient, remainder, small, spec}:
      spec

def Grids.quotient_bound(+size: Nat, +quotient: Nat, below: N.Natural.Le(1n+Nat.mul(quotient, 1n+size), Nat.mul(1n+size, 1n+size)),
  decision: Or(N.Natural.Le(quotient, size), N.Natural.Le(quotient, size) -> Empty)) -> N.Natural.Le(quotient, size):
  match decision:
    case Inl{le}:
      le
    case Inr{above}:
      Empty.absurd(N.Natural.Le(quotient, size), N.Natural.not_successor_le_self(Nat.mul(quotient, 1n+size),
        N.Natural.le_transitive(1n+Nat.mul(quotient, 1n+size), Nat.mul(1n+size, 1n+size), Nat.mul(quotient, 1n+size), below,
          N.Natural.le_mul_right(1n+size, quotient, 1n+size, Grids.successor_le(size, quotient, above)))))

def Grids.quotient_small(+size: Nat, +index: Nat, place: Grids.Place<size, index>, bound: N.Natural.Le(1n+index, Nat.mul(1n+size, 1n+size))) ->
  N.Natural.Le(Grids.quotient(size, index, place), size):
  match place:
    case Place{+quotient, +remainder, small, spec}:
      +before: Nat = Nat.mul(quotient, 1n+size)
      Grids.quotient_bound(size, quotient,
        N.Natural.le_transitive(1n+before, 1n+index, Nat.mul(1n+size, 1n+size),
          N.Natural.le_congruent(before, Nat.add(before, remainder), before, index, N.Natural.le_add_right(before, remainder), {==}, spec), bound),
        N.Natural.le_decidable(quotient, size))

def Grids.square(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +index: Nat) -> P.Problem.Square<F, field>:
  Q.Grid.cell(~F, ~field, Grids.quotient(size, index, Grids.place(size, index)), Grids.remainder(size, index, Grids.place(size, index)))

def Grids.apart_quotients(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +left: Nat, +right: Nat, +rl: Nat, +ql: Nat, +rr: Nat, +qr: Nat,
  +spec_left: {Nat.add(Nat.mul(ql, 1n+size), rl) == left : Nat}, +spec_right: {Nat.add(Nat.mul(qr, 1n+size), rr) == right : Nat},
  +remainders: {rl == rr : Nat}, different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Q.Grid.cell(~F, ~field, ql, rl), point>,
  second: P.Problem.InteriorContainment<F, field, Q.Grid.cell(~F, ~field, qr, rr), point>,
  below: Or(N.Natural.Le(1n+ql, qr), N.Natural.Le(1n+ql, qr) -> Empty), above: Or(N.Natural.Le(1n+qr, ql), N.Natural.Le(1n+qr, ql) -> Empty)) -> Empty:
  match below:
    case Inl{gap}:
      Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, ql)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rl)),
        A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, qr)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rr)),
        Q.Grid.offset_gap(~F, ~field, ql, qr, gap), point, first, second)
    case Inr{low}:
      match above:
        case Inl{gap}:
          Q.Grid.separated_x(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, qr)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rr)),
            A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, ql)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rl)),
            Q.Grid.offset_gap(~F, ~field, qr, ql, gap), point, second, first)
        case Inr{high}:
          +quotients: {ql == qr : Nat} = N.Natural.le_antisymmetric(ql, qr, Grids.le_of_not_successor_le(qr, ql, high), Grids.le_of_not_successor_le(ql, qr, low))
          different(Equal.trans(Nat, left, Nat.add(Nat.mul(ql, 1n+size), rl), right, Equal.sym(Nat, Nat.add(Nat.mul(ql, 1n+size), rl), left, spec_left),
            Equal.trans(Nat, Nat.add(Nat.mul(ql, 1n+size), rl), Nat.add(Nat.mul(qr, 1n+size), rr), right,
              N.Natural.eq_add_congruent(Nat.mul(ql, 1n+size), rl, Nat.mul(qr, 1n+size), rr, N.Natural.eq_mul_congruent(ql, 1n+size, qr, 1n+size, quotients, {==}), remainders),
              spec_right)))

def Grids.apart(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +left: Nat, +right: Nat, +rl: Nat, +ql: Nat, +rr: Nat, +qr: Nat,
  +spec_left: {Nat.add(Nat.mul(ql, 1n+size), rl) == left : Nat}, +spec_right: {Nat.add(Nat.mul(qr, 1n+size), rr) == right : Nat},
  different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Q.Grid.cell(~F, ~field, ql, rl), point>,
  second: P.Problem.InteriorContainment<F, field, Q.Grid.cell(~F, ~field, qr, rr), point>,
  below: Or(N.Natural.Le(1n+rl, rr), N.Natural.Le(1n+rl, rr) -> Empty), above: Or(N.Natural.Le(1n+rr, rl), N.Natural.Le(1n+rr, rl) -> Empty)) -> Empty:
  match below:
    case Inl{gap}:
      Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, ql)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rl)),
        A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, qr)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rr)),
        Q.Grid.offset_gap(~F, ~field, rl, rr, gap), point, first, second)
    case Inr{low}:
      match above:
        case Inl{gap}:
          Q.Grid.separated_y(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, qr)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rr)),
            A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, ql)), A.Algebra.add(~F, ~field, A.Algebra.half(~F, ~field), R.FieldRing.of_nat(~F, ~field, rl)),
            Q.Grid.offset_gap(~F, ~field, rr, rl, gap), point, second, first)
        case Inr{high}:
          Grids.apart_quotients(~F, ~field, size, left, right, rl, ql, rr, qr, spec_left, spec_right,
            N.Natural.le_antisymmetric(rl, rr, Grids.le_of_not_successor_le(rr, rl, high), Grids.le_of_not_successor_le(rl, rr, low)),
            different, point, first, second, N.Natural.le_decidable(1n+ql, qr), N.Natural.le_decidable(1n+qr, ql))

def Grids.disjoint(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +left: Nat, +right: Nat, different: {left == right : Nat} -> Empty, +point: P.Problem.Point<F>,
  first: P.Problem.InteriorContainment<F, field, Grids.square(~F, ~field, size, left), point>,
  second: P.Problem.InteriorContainment<F, field, Grids.square(~F, ~field, size, right), point>) -> Empty:
  +rl: Nat = Grids.remainder(size, left, Grids.place(size, left))
  +ql: Nat = Grids.quotient(size, left, Grids.place(size, left))
  +rr: Nat = Grids.remainder(size, right, Grids.place(size, right))
  +qr: Nat = Grids.quotient(size, right, Grids.place(size, right))
  Grids.apart(~F, ~field, size, left, right, rl, ql, rr, qr, Grids.spec(size, left, Grids.place(size, left)), Grids.spec(size, right, Grids.place(size, right)),
    different, point, first, second, N.Natural.le_decidable(1n+rl, rr), N.Natural.le_decidable(1n+rr, rl))

def Grids.fits(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +index: Nat, bound: N.Natural.Le(1n+index, Nat.mul(1n+size, 1n+size)), +point: P.Problem.Point<F>,
  containment: P.Problem.Containment<F, field, Grids.square(~F, ~field, size, index), point>) ->
  P.Problem.InContainer<F, field, R.FieldRing.of_nat(~F, ~field, 1n+size), point>:
  Q.Grid.fits(~F, ~field, size, Grids.quotient(size, index, Grids.place(size, index)), Grids.remainder(size, index, Grids.place(size, index)),
    Grids.quotient_small(size, index, Grids.place(size, index), bound), Grids.remainder_small(size, index, Grids.place(size, index)), point, containment)

def Grids.packing(~F: Kind(&2), ~field: K.Field<F>, +size: Nat, +count: Nat, +fits: N.Natural.Le(count, Nat.mul(1n+size, 1n+size))) ->
  P.Problem.Packing<F, field, count, R.FieldRing.of_nat(~F, ~field, 1n+size)>:
  P.Packing{
    index => Grids.square(~F, ~field, size, index),
    O.FieldOrder.zero_le_of_nat(~F, ~field, 1n+size),
    +index => bound => point => containment =>
      Grids.fits(~F, ~field, size, index, N.Natural.le_transitive(1n+index, count, Nat.mul(1n+size, 1n+size), bound, fits), point, containment),
    +left => +right => left_bound => right_bound => different => point => first => second =>
      Grids.disjoint(~F, ~field, size, left, right, different, point, first, second)
  }

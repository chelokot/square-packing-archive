import Base
import ./bend-math/Field.bend as K
import ./bend-math/FieldAlgebra.bend as A
import ./bend-math/FieldRing.bend as R
import ./bend-math/FieldOrder.bend as O
import ./bend-math/Ring.bend as Z
import ./Problem.bend as P
import ./Geometry.bend as G
import ./bend-math/Certificate.bend as C

def Symmetry.norm(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F) -> F:
  A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, cosine, cosine), A.Algebra.mul(~F, ~field, sine, sine))

def Symmetry.below_like(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F, +new_cosine: F, +new_sine: F,
  same: A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, new_cosine, new_sine), Symmetry.norm(~F, ~field, cosine, sine)),
  unit_below: A.Algebra.le(~F, ~field, Symmetry.norm(~F, ~field, cosine, sine), A.Algebra.one(~F, ~field))) -> A.Algebra.le(~F, ~field, Symmetry.norm(~F, ~field, new_cosine, new_sine), A.Algebra.one(~F, ~field)):
  (forward, backward) = same
  K.Field.le_transitive(F, field)(Symmetry.norm(~F, ~field, new_cosine, new_sine), Symmetry.norm(~F, ~field, cosine, sine), A.Algebra.one(~F, ~field), forward, unit_below)

def Symmetry.above_like(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F, +new_cosine: F, +new_sine: F,
  same: A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, new_cosine, new_sine), Symmetry.norm(~F, ~field, cosine, sine)),
  unit_above: A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), Symmetry.norm(~F, ~field, cosine, sine))) -> A.Algebra.le(~F, ~field, A.Algebra.one(~F, ~field), Symmetry.norm(~F, ~field, new_cosine, new_sine)):
  (forward, backward) = same
  K.Field.le_transitive(F, field)(A.Algebra.one(~F, ~field), Symmetry.norm(~F, ~field, cosine, sine), Symmetry.norm(~F, ~field, new_cosine, new_sine), unit_above, backward)

def Symmetry.two(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> R.FieldRing.Values<F>:
  R.Value{a, R.Value{b, R.NoValues{}}}

def Symmetry.swapped_norm(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F) -> A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, sine, cosine), Symmetry.norm(~F, ~field, cosine, sine)):
  R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, cosine, sine),
    R.Plus{R.Multiply{R.Variable{1n}, R.Variable{1n}}, R.Multiply{R.Variable{0n}, R.Variable{0n}}},
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}}, {==})

def Symmetry.turned_norm(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F) -> A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, A.Algebra.neg(~F, ~field, sine), cosine), Symmetry.norm(~F, ~field, cosine, sine)):
  R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, cosine, sine),
    R.Plus{R.Multiply{R.Negate{R.Variable{1n}}, R.Negate{R.Variable{1n}}}, R.Multiply{R.Variable{0n}, R.Variable{0n}}},
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}}, {==})

def Symmetry.mirrored_cosine_norm(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F) -> A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, A.Algebra.neg(~F, ~field, cosine), sine), Symmetry.norm(~F, ~field, cosine, sine)):
  R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, cosine, sine),
    R.Plus{R.Multiply{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{0n}}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}},
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}}, {==})

def Symmetry.mirrored_sine_norm(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F) -> A.Algebra.Same(~F, ~field, Symmetry.norm(~F, ~field, cosine, A.Algebra.neg(~F, ~field, sine)), Symmetry.norm(~F, ~field, cosine, sine)):
  R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, cosine, sine),
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Negate{R.Variable{1n}}, R.Negate{R.Variable{1n}}}},
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}}, {==})

def Symmetry.translate(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, frame}:
      P.Square{P.Point{A.Algebra.add(~F, ~field, center_x, horizontal), A.Algebra.add(~F, ~field, center_y, vertical)}, frame}

def Symmetry.swap(~F: Kind(&2), ~field: K.Field<F>, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}}:
      P.Square{P.Point{center_y, center_x}, P.Frame{sine, cosine,
        Symmetry.below_like(~F, ~field, cosine, sine, sine, cosine, Symmetry.swapped_norm(~F, ~field, cosine, sine), unit_below),
        Symmetry.above_like(~F, ~field, cosine, sine, sine, cosine, Symmetry.swapped_norm(~F, ~field, cosine, sine), unit_above)}}

def Symmetry.turn(~F: Kind(&2), ~field: K.Field<F>, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{center, P.Frame{+cosine, +sine, +unit_below, +unit_above}}:
      P.Square{center, P.Frame{A.Algebra.neg(~F, ~field, sine), cosine,
        Symmetry.below_like(~F, ~field, cosine, sine, A.Algebra.neg(~F, ~field, sine), cosine, Symmetry.turned_norm(~F, ~field, cosine, sine), unit_below),
        Symmetry.above_like(~F, ~field, cosine, sine, A.Algebra.neg(~F, ~field, sine), cosine, Symmetry.turned_norm(~F, ~field, cosine, sine), unit_above)}}

def Symmetry.reflect_x(~F: Kind(&2), ~field: K.Field<F>, +sum: F, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}}:
      P.Square{P.Point{A.Algebra.add(~F, ~field, sum, A.Algebra.neg(~F, ~field, center_x)), center_y}, P.Frame{A.Algebra.neg(~F, ~field, cosine), sine,
        Symmetry.below_like(~F, ~field, cosine, sine, A.Algebra.neg(~F, ~field, cosine), sine, Symmetry.mirrored_cosine_norm(~F, ~field, cosine, sine), unit_below),
        Symmetry.above_like(~F, ~field, cosine, sine, A.Algebra.neg(~F, ~field, cosine), sine, Symmetry.mirrored_cosine_norm(~F, ~field, cosine, sine), unit_above)}}

def Symmetry.reflect_y(~F: Kind(&2), ~field: K.Field<F>, +sum: F, square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  match square:
    case P.Square{P.Point{center_x, center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}}:
      P.Square{P.Point{center_x, A.Algebra.add(~F, ~field, sum, A.Algebra.neg(~F, ~field, center_y))}, P.Frame{cosine, A.Algebra.neg(~F, ~field, sine),
        Symmetry.below_like(~F, ~field, cosine, sine, cosine, A.Algebra.neg(~F, ~field, sine), Symmetry.mirrored_sine_norm(~F, ~field, cosine, sine), unit_below),
        Symmetry.above_like(~F, ~field, cosine, sine, cosine, A.Algebra.neg(~F, ~field, sine), Symmetry.mirrored_sine_norm(~F, ~field, cosine, sine), unit_above)}}

def Symmetry.translate_point(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{A.Algebra.add(~F, ~field, x, horizontal), A.Algebra.add(~F, ~field, y, vertical)}

def Symmetry.swap_point(-F: Kind(&2), point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{y, x}

def Symmetry.reflect_x_point(~F: Kind(&2), ~field: K.Field<F>, +sum: F, point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{A.Algebra.add(~F, ~field, sum, A.Algebra.neg(~F, ~field, x)), y}

def Symmetry.reflect_y_point(~F: Kind(&2), ~field: K.Field<F>, +sum: F, point: P.Problem.Point<F>) -> P.Problem.Point<F>:
  match point:
    case P.Point{x, y}:
      P.Point{x, A.Algebra.add(~F, ~field, sum, A.Algebra.neg(~F, ~field, y))}

def Symmetry.negate_bound(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, a, A.Algebra.neg(~F, ~field, b))) -> A.Algebra.le(~F, ~field, b, A.Algebra.neg(~F, ~field, a)):
  A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, b)), A.Algebra.neg(~F, ~field, a), b, A.Algebra.neg(~F, ~field, a), O.FieldOrder.le_negate(~F, ~field, a, A.Algebra.neg(~F, ~field, b), below),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, b, a), R.Negate{R.Negate{R.Variable{0n}}}, R.Variable{0n}, {==}),
    A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, a)))

def Symmetry.negate_bound_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, a), b)) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), a):
  A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, a)), A.Algebra.neg(~F, ~field, b), a, O.FieldOrder.le_negate(~F, ~field, A.Algebra.neg(~F, ~field, a), b, below),
    A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, b)),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, a, b), R.Negate{R.Negate{R.Variable{0n}}}, R.Variable{0n}, {==}))

def Symmetry.le_same_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: A.Algebra.Same(~F, ~field, a, b), below: A.Algebra.le(~F, ~field, b, c)) -> A.Algebra.le(~F, ~field, a, c):
  (forward, backward) = same
  K.Field.le_transitive(F, field)(a, b, c, forward, below)

def Symmetry.le_same_right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: A.Algebra.Same(~F, ~field, c, b), below: A.Algebra.le(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, a, c):
  (forward, backward) = same
  K.Field.le_transitive(F, field)(a, b, c, below, backward)

def Symmetry.local_keep(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_x), same_y: A.Algebra.Same(~F, ~field, new_y, local_y), local: G.Geometry.Local<F, field, local_x, local_y>) ->
  G.Geometry.Local<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.Local{x_at_most, x_at_least, y_at_most, y_at_least}:
      G.Local{
        K.Field.le_transitive(F, field)(new_x, local_x, A.Algebra.half(~F, ~field), x_forward, x_at_most),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x, new_x, x_at_least, x_backward),
        K.Field.le_transitive(F, field)(new_y, local_y, A.Algebra.half(~F, ~field), y_forward, y_at_most),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y, new_y, y_at_least, y_backward)}

def Symmetry.local_negate_y(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_x), same_y: A.Algebra.Same(~F, ~field, new_y, A.Algebra.neg(~F, ~field, local_y)), local: G.Geometry.Local<F, field, local_x, local_y>) ->
  G.Geometry.Local<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.Local{x_at_most, x_at_least, y_at_most, y_at_least}:
      G.Local{
        K.Field.le_transitive(F, field)(new_x, local_x, A.Algebra.half(~F, ~field), x_forward, x_at_most),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x, new_x, x_at_least, x_backward),
        K.Field.le_transitive(F, field)(new_y, A.Algebra.neg(~F, ~field, local_y), A.Algebra.half(~F, ~field), y_forward, Symmetry.negate_bound_left(~F, ~field, A.Algebra.half(~F, ~field), local_y, y_at_least)),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, local_y), new_y, O.FieldOrder.le_negate(~F, ~field, local_y, A.Algebra.half(~F, ~field), y_at_most), y_backward)}

def Symmetry.local_turn(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_y), same_y: A.Algebra.Same(~F, ~field, new_y, A.Algebra.neg(~F, ~field, local_x)), local: G.Geometry.Local<F, field, local_x, local_y>) ->
  G.Geometry.Local<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.Local{x_at_most, x_at_least, y_at_most, y_at_least}:
      G.Local{
        K.Field.le_transitive(F, field)(new_x, local_y, A.Algebra.half(~F, ~field), x_forward, y_at_most),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_y, new_x, y_at_least, x_backward),
        K.Field.le_transitive(F, field)(new_y, A.Algebra.neg(~F, ~field, local_x), A.Algebra.half(~F, ~field), y_forward, Symmetry.negate_bound_left(~F, ~field, A.Algebra.half(~F, ~field), local_x, x_at_least)),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, local_x), new_y, O.FieldOrder.le_negate(~F, ~field, local_x, A.Algebra.half(~F, ~field), x_at_most), y_backward)}

def Symmetry.unnegate(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, below: A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, b))) -> A.Algebra.le(~F, ~field, b, a):
  A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, b)), A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, a)), b, a, O.FieldOrder.le_negate(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, b), below),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, b, a), R.Negate{R.Negate{R.Variable{0n}}}, R.Variable{0n}, {==}),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, a, b), R.Negate{R.Negate{R.Variable{0n}}}, R.Variable{0n}, {==}))

def Symmetry.strict_keep(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_x), same_y: A.Algebra.Same(~F, ~field, new_y, local_y), local: G.Geometry.StrictLocal<F, field, local_x, local_y>) ->
  G.Geometry.StrictLocal<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.StrictLocal{x_below, x_above, y_below, y_above}:
      G.StrictLocal{
        reached => x_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_x, local_x, reached, x_forward)),
        reached => x_above(K.Field.le_transitive(F, field)(local_x, new_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x_backward, reached)),
        reached => y_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_y, local_y, reached, y_forward)),
        reached => y_above(K.Field.le_transitive(F, field)(local_y, new_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y_backward, reached))}

def Symmetry.strict_negate_y(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_x), same_y: A.Algebra.Same(~F, ~field, new_y, A.Algebra.neg(~F, ~field, local_y)), local: G.Geometry.StrictLocal<F, field, local_x, local_y>) ->
  G.Geometry.StrictLocal<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.StrictLocal{x_below, x_above, y_below, y_above}:
      G.StrictLocal{
        reached => x_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_x, local_x, reached, x_forward)),
        reached => x_above(K.Field.le_transitive(F, field)(local_x, new_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x_backward, reached)),
        reached => y_above(Symmetry.negate_bound(~F, ~field, A.Algebra.half(~F, ~field), local_y, K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_y, A.Algebra.neg(~F, ~field, local_y), reached, y_forward))),
        reached => y_below(Symmetry.unnegate(~F, ~field, local_y, A.Algebra.half(~F, ~field), K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, local_y), new_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y_backward, reached)))}

def Symmetry.strict_turn(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, local_y), same_y: A.Algebra.Same(~F, ~field, new_y, A.Algebra.neg(~F, ~field, local_x)), local: G.Geometry.StrictLocal<F, field, local_x, local_y>) ->
  G.Geometry.StrictLocal<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.StrictLocal{x_below, x_above, y_below, y_above}:
      G.StrictLocal{
        reached => y_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_x, local_y, reached, x_forward)),
        reached => y_above(K.Field.le_transitive(F, field)(local_y, new_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x_backward, reached)),
        reached => x_above(Symmetry.negate_bound(~F, ~field, A.Algebra.half(~F, ~field), local_x, K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_y, A.Algebra.neg(~F, ~field, local_x), reached, y_forward))),
        reached => x_below(Symmetry.unnegate(~F, ~field, local_x, A.Algebra.half(~F, ~field), K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, local_x), new_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y_backward, reached)))}

def Symmetry.values(~F: Kind(&2), ~field: K.Field<F>, +center_x: F, +center_y: F, +cosine: F, +sine: F, +x: F, +y: F, +first: F, +second: F) -> R.FieldRing.Values<F>:
  R.Value{center_x, R.Value{center_y, R.Value{cosine, R.Value{sine, R.Value{x, R.Value{y, R.Value{first, R.Value{second, R.NoValues{}}}}}}}}}

def Symmetry.translate_contains(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.translate(~F, ~field, horizontal, vertical, square), Symmetry.translate_point(~F, ~field, horizontal, vertical, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, horizontal, vertical)
      G.Geometry.local_contains(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y}),
        Symmetry.local_keep(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{4n}, R.Variable{6n}}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Variable{7n}}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{4n}, R.Variable{6n}}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Variable{7n}}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          G.Geometry.contains_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.translate_interior(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, square, point>) ->
  P.Problem.InteriorContainment<F, field, Symmetry.translate(~F, ~field, horizontal, vertical, square), Symmetry.translate_point(~F, ~field, horizontal, vertical, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, horizontal, vertical)
      G.Geometry.local_interior(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y}),
        Symmetry.strict_keep(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), Symmetry.translate_point(~F, ~field, horizontal, vertical, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{4n}, R.Variable{6n}}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Variable{7n}}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{4n}, R.Variable{6n}}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Variable{7n}}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          G.Geometry.interior_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.swap_contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.swap(~F, ~field, square), Symmetry.swap_point(F, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{3n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.swap_interior(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, square, point>) ->
  P.Problem.InteriorContainment<F, field, Symmetry.swap(~F, ~field, square), Symmetry.swap_point(F, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.swap(~F, ~field, original), Symmetry.swap_point(F, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{3n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.turn_contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.turn(~F, ~field, square), point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y},
        Symmetry.local_turn(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{3n}}}}, R.Negate{R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.turn_interior(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, square, point>) ->
  P.Problem.InteriorContainment<F, field, Symmetry.turn(~F, ~field, square), point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y},
        Symmetry.strict_turn(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{3n}}}}, R.Negate{R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.reflect_x_contains(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.reflect_x(~F, ~field, sum, square), Symmetry.reflect_x_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}, R.Negate{R.Variable{2n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{2n}}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.reflect_x_interior(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, square, point>) ->
  P.Problem.InteriorContainment<F, field, Symmetry.reflect_x(~F, ~field, sum, square), Symmetry.reflect_x_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}, R.Negate{R.Variable{2n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{2n}}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.reflect_y_contains(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.reflect_y(~F, ~field, sum, square), Symmetry.reflect_y_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Negate{R.Variable{3n}}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.reflect_y_interior(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, square, point>) ->
  P.Problem.InteriorContainment<F, field, Symmetry.reflect_y(~F, ~field, sum, square), Symmetry.reflect_y_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Negate{R.Variable{3n}}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, original, P.Point{x, y}, inside)))

def Symmetry.local_unturn(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, A.Algebra.neg(~F, ~field, local_y)), same_y: A.Algebra.Same(~F, ~field, new_y, local_x), local: G.Geometry.Local<F, field, local_x, local_y>) ->
  G.Geometry.Local<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.Local{x_at_most, x_at_least, y_at_most, y_at_least}:
      G.Local{
        K.Field.le_transitive(F, field)(new_x, A.Algebra.neg(~F, ~field, local_y), A.Algebra.half(~F, ~field), x_forward, Symmetry.negate_bound_left(~F, ~field, A.Algebra.half(~F, ~field), local_y, y_at_least)),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), A.Algebra.neg(~F, ~field, local_y), new_x, O.FieldOrder.le_negate(~F, ~field, local_y, A.Algebra.half(~F, ~field), y_at_most), x_backward),
        K.Field.le_transitive(F, field)(new_y, local_x, A.Algebra.half(~F, ~field), y_forward, x_at_most),
        K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), local_x, new_y, x_at_least, y_backward)}

def Symmetry.strict_unturn(~F: Kind(&2), ~field: K.Field<F>, +local_x: F, +local_y: F, +new_x: F, +new_y: F,
  same_x: A.Algebra.Same(~F, ~field, new_x, A.Algebra.neg(~F, ~field, local_y)), same_y: A.Algebra.Same(~F, ~field, new_y, local_x), local: G.Geometry.StrictLocal<F, field, local_x, local_y>) ->
  G.Geometry.StrictLocal<F, field, new_x, new_y>:
  (x_forward, x_backward) = same_x
  (y_forward, y_backward) = same_y
  match local:
    case G.StrictLocal{x_below, x_above, y_below, y_above}:
      G.StrictLocal{
        reached => y_above(Symmetry.negate_bound(~F, ~field, A.Algebra.half(~F, ~field), local_y, K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_x, A.Algebra.neg(~F, ~field, local_y), reached, x_forward))),
        reached => y_below(Symmetry.unnegate(~F, ~field, local_y, A.Algebra.half(~F, ~field), K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, local_y), new_x, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), x_backward, reached))),
        reached => x_below(K.Field.le_transitive(F, field)(A.Algebra.half(~F, ~field), new_y, local_x, reached, y_forward)),
        reached => x_above(K.Field.le_transitive(F, field)(local_x, new_y, A.Algebra.neg(~F, ~field, A.Algebra.half(~F, ~field)), y_backward, reached))}

def Symmetry.translate_contains_back(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.translate(~F, ~field, horizontal, vertical, square), point>) ->
  P.Problem.Containment<F, field, square, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, horizontal, vertical)
      G.Geometry.local_contains(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y}),
        Symmetry.local_keep(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{4n}, R.Negate{R.Variable{6n}}}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Negate{R.Variable{7n}}}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{4n}, R.Negate{R.Variable{6n}}}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Negate{R.Variable{7n}}}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{2n}}}, {==}),
          G.Geometry.contains_local(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}, inside)))

def Symmetry.translate_interior_back(~F: Kind(&2), ~field: K.Field<F>, +horizontal: F, +vertical: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.translate(~F, ~field, horizontal, vertical, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, horizontal, vertical)
      G.Geometry.local_interior(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y}),
        Symmetry.strict_keep(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.translate_point(~F, ~field, A.Algebra.neg(~F, ~field, horizontal), A.Algebra.neg(~F, ~field, vertical), P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{4n}, R.Negate{R.Variable{6n}}}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Negate{R.Variable{7n}}}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{4n}, R.Negate{R.Variable{6n}}}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{5n}, R.Negate{R.Variable{7n}}}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{0n}, R.Variable{6n}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{1n}, R.Variable{7n}}}}, R.Variable{2n}}}, {==}),
          G.Geometry.interior_local(~F, ~field, Symmetry.translate(~F, ~field, horizontal, vertical, original), P.Point{x, y}, inside)))

def Symmetry.swap_contains_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.swap(~F, ~field, square), point>) ->
  P.Problem.Containment<F, field, square, Symmetry.swap_point(F, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{3n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}, inside)))

def Symmetry.swap_interior_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.swap(~F, ~field, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Symmetry.swap_point(F, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.swap_point(F, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{1n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{0n}}}, R.Variable{3n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, Symmetry.swap(~F, ~field, original), P.Point{x, y}, inside)))

def Symmetry.turn_contains_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.turn(~F, ~field, square), point>) ->
  P.Problem.Containment<F, field, square, point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, original, P.Point{x, y},
        Symmetry.local_unturn(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{3n}}}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          G.Geometry.contains_local(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}, inside)))

def Symmetry.turn_interior_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.turn(~F, ~field, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, point>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, original, P.Point{x, y},
        Symmetry.strict_unturn(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, P.Point{x, y}), G.Geometry.local_y(~F, ~field, original, P.Point{x, y}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{3n}}}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, {==}),
          G.Geometry.interior_local(~F, ~field, Symmetry.turn(~F, ~field, original), P.Point{x, y}, inside)))

def Symmetry.reflect_x_contains_back(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.reflect_x(~F, ~field, sum, square), point>) ->
  P.Problem.Containment<F, field, square, Symmetry.reflect_x_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}, R.Negate{R.Variable{2n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{2n}}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}, inside)))

def Symmetry.reflect_x_interior_back(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.reflect_x(~F, ~field, sum, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Symmetry.reflect_x_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.reflect_x_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}, R.Negate{R.Variable{2n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{4n}}}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{0n}}}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Variable{2n}}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, Symmetry.reflect_x(~F, ~field, sum, original), P.Point{x, y}, inside)))

def Symmetry.reflect_y_contains_back(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.reflect_y(~F, ~field, sum, square), point>) ->
  P.Problem.Containment<F, field, square, Symmetry.reflect_y_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_contains(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.local_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Negate{R.Variable{3n}}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.contains_local(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}, inside)))

def Symmetry.reflect_y_interior_back(~F: Kind(&2), ~field: K.Field<F>, +sum: F, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.reflect_y(~F, ~field, sum, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, Symmetry.reflect_y_point(~F, ~field, sum, point)>:
  match square point:
    case P.Square{P.Point{+center_x, +center_y}, P.Frame{+cosine, +sine, +unit_below, +unit_above}} P.Point{+x, +y}:
      +original: P.Problem.Square<F, field> = P.Square{P.Point{center_x, center_y}, P.Frame{cosine, sine, unit_below, unit_above}}
      +values: R.FieldRing.Values<F> = Symmetry.values(~F, ~field, center_x, center_y, cosine, sine, x, y, sum, A.Algebra.zero(~F, ~field))
      G.Geometry.local_interior(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y}),
        Symmetry.strict_negate_y(~F, ~field,
          G.Geometry.local_x(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_y(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}),
          G.Geometry.local_x(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})), G.Geometry.local_y(~F, ~field, original, Symmetry.reflect_y_point(~F, ~field, sum, P.Point{x, y})),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Variable{1n}}}, R.Variable{3n}}}, R.Plus{R.Multiply{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}, R.Variable{2n}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Negate{R.Variable{3n}}}}, {==}),
          R.FieldRing.equal(~F, ~field, values, R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Variable{3n}}, R.Multiply{R.Plus{R.Plus{R.Variable{6n}, R.Negate{R.Variable{5n}}}, R.Negate{R.Variable{1n}}}, R.Variable{2n}}}, R.Negate{R.Plus{R.Multiply{R.Negate{R.Plus{R.Variable{4n}, R.Negate{R.Variable{0n}}}}, R.Negate{R.Variable{3n}}}, R.Multiply{R.Plus{R.Variable{5n}, R.Negate{R.Plus{R.Variable{6n}, R.Negate{R.Variable{1n}}}}}, R.Variable{2n}}}}, {==}),
          G.Geometry.interior_local(~F, ~field, Symmetry.reflect_y(~F, ~field, sum, original), P.Point{x, y}, inside)))

def Symmetry.Fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F) -> Type:
  @point: P.Problem.Point<F> -> P.Problem.Containment<F, field, square, point> -> P.Problem.InContainer<F, field, side, point>

def Symmetry.flipped_low(~F: Kind(&2), ~field: K.Field<F>, +side: F, +x: F, below: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)))) -> A.Algebra.le(~F, ~field, x, side):
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), x), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)), x), x, side, K.Field.le_add(F, field)(A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)), x, below),
    A.Algebra.zero_add(~F, ~field, x),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, side, x), R.Plus{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, R.Variable{1n}}, R.Variable{0n}, {==}))

def Symmetry.flipped_high(~F: Kind(&2), ~field: K.Field<F>, +side: F, +x: F, above: A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)), side)) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), x):
  +shift: F = A.Algebra.add(~F, ~field, x, A.Algebra.neg(~F, ~field, side))
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)), shift), A.Algebra.add(~F, ~field, side, shift), A.Algebra.zero(~F, ~field), x, K.Field.le_add(F, field)(A.Algebra.add(~F, ~field, side, A.Algebra.neg(~F, ~field, x)), side, shift, above),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, side, x),
      R.Plus{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, R.Plus{R.Variable{1n}, R.Negate{R.Variable{0n}}}}, R.Number{0n}, {==}),
    R.FieldRing.equal(~F, ~field, Symmetry.two(~F, ~field, side, x),
      R.Plus{R.Variable{0n}, R.Plus{R.Variable{1n}, R.Negate{R.Variable{0n}}}}, R.Variable{1n}, {==}))

def Symmetry.container_swap(~F: Kind(&2), ~field: K.Field<F>, +side: F, +point: P.Problem.Point<F>,
  inside: P.Problem.InContainer<F, field, side, Symmetry.swap_point(F, point)>) -> P.Problem.InContainer<F, field, side, point>:
  match point inside:
    case P.Point{x, y} P.InContainer{left, right, bottom, top}:
      P.InContainer{bottom, top, left, right}

def Symmetry.container_reflect_x(~F: Kind(&2), ~field: K.Field<F>, +side: F, +point: P.Problem.Point<F>,
  inside: P.Problem.InContainer<F, field, side, Symmetry.reflect_x_point(~F, ~field, side, point)>) -> P.Problem.InContainer<F, field, side, point>:
  match point inside:
    case P.Point{+x, +y} P.InContainer{left, right, bottom, top}:
      P.InContainer{Symmetry.flipped_high(~F, ~field, side, x, right), Symmetry.flipped_low(~F, ~field, side, x, left), bottom, top}

def Symmetry.container_reflect_y(~F: Kind(&2), ~field: K.Field<F>, +side: F, +point: P.Problem.Point<F>,
  inside: P.Problem.InContainer<F, field, side, Symmetry.reflect_y_point(~F, ~field, side, point)>) -> P.Problem.InContainer<F, field, side, point>:
  match point inside:
    case P.Point{+x, +y} P.InContainer{left, right, bottom, top}:
      P.InContainer{left, right, Symmetry.flipped_high(~F, ~field, side, y, top), Symmetry.flipped_low(~F, ~field, side, y, bottom)}

def Symmetry.swap_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, square, side)) ->
  Symmetry.Fits(~F, ~field, Symmetry.swap(~F, ~field, square), side):
  +point => inside => Symmetry.container_swap(~F, ~field, side, point,
    fits(Symmetry.swap_point(F, point), Symmetry.swap_contains_back(~F, ~field, square, point, inside)))

def Symmetry.swap_fits_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, Symmetry.swap(~F, ~field, square), side)) ->
  Symmetry.Fits(~F, ~field, square, side):
  +point => inside => Symmetry.container_swap(~F, ~field, side, point,
    fits(Symmetry.swap_point(F, point), Symmetry.swap_contains(~F, ~field, square, point, inside)))

def Symmetry.reflect_x_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, square, side)) ->
  Symmetry.Fits(~F, ~field, Symmetry.reflect_x(~F, ~field, side, square), side):
  +point => inside => Symmetry.container_reflect_x(~F, ~field, side, point,
    fits(Symmetry.reflect_x_point(~F, ~field, side, point), Symmetry.reflect_x_contains_back(~F, ~field, side, square, point, inside)))

def Symmetry.reflect_x_fits_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, Symmetry.reflect_x(~F, ~field, side, square), side)) ->
  Symmetry.Fits(~F, ~field, square, side):
  +point => inside => Symmetry.container_reflect_x(~F, ~field, side, point,
    fits(Symmetry.reflect_x_point(~F, ~field, side, point), Symmetry.reflect_x_contains(~F, ~field, side, square, point, inside)))

def Symmetry.reflect_y_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, square, side)) ->
  Symmetry.Fits(~F, ~field, Symmetry.reflect_y(~F, ~field, side, square), side):
  +point => inside => Symmetry.container_reflect_y(~F, ~field, side, point,
    fits(Symmetry.reflect_y_point(~F, ~field, side, point), Symmetry.reflect_y_contains_back(~F, ~field, side, square, point, inside)))

def Symmetry.reflect_y_fits_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, Symmetry.reflect_y(~F, ~field, side, square), side)) ->
  Symmetry.Fits(~F, ~field, square, side):
  +point => inside => Symmetry.container_reflect_y(~F, ~field, side, point,
    fits(Symmetry.reflect_y_point(~F, ~field, side, point), Symmetry.reflect_y_contains(~F, ~field, side, square, point, inside)))

def Symmetry.turn_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, square, side)) ->
  Symmetry.Fits(~F, ~field, Symmetry.turn(~F, ~field, square), side):
  +point => inside => fits(point, Symmetry.turn_contains_back(~F, ~field, square, point, inside))

def Symmetry.turn_fits_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, Symmetry.turn(~F, ~field, square), side)) ->
  Symmetry.Fits(~F, ~field, square, side):
  +point => inside => fits(point, Symmetry.turn_contains(~F, ~field, square, point, inside))

def Symmetry.quadrant_by(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>,
  cosine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)) -> Empty),
  sine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)) -> Empty)) ->
  P.Problem.Square<F, field>:
  match cosine_sign sine_sign:
    case Inl{a} Inl{b}:
      square
    case Inl{a} Inr{b}:
      Symmetry.turn(~F, ~field, square)
    case Inr{a} Inl{b}:
      Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, square)))
    case Inr{a} Inr{b}:
      Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, square))

def Symmetry.first_quadrant(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>) -> P.Problem.Square<F, field>:
  Symmetry.quadrant_by(~F, ~field, square,
    K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)))

def Symmetry.nonpositive(~F: Kind(&2), ~field: K.Field<F>, +a: F, negative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), a) -> Empty) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, a)):
  A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.neg(~F, ~field, a), A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, a), O.FieldOrder.le_negate(~F, ~field, a, A.Algebra.zero(~F, ~field), O.FieldOrder.le_of_lt(~F, ~field, a, A.Algebra.zero(~F, ~field), negative)),
    R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Negate{R.Number{0n}}, R.Number{0n}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, a)))

def Symmetry.double_negation(~F: Kind(&2), ~field: K.Field<F>, +a: F, below: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), a)) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, a))):
  A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), a, A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, A.Algebra.neg(~F, ~field, a)), below, A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field)),
    R.FieldRing.equal(~F, ~field, R.Value{a, R.NoValues{}}, R.Variable{0n}, R.Negate{R.Negate{R.Variable{0n}}}, {==}))

def Symmetry.quadrant_signs(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>,
  cosine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)) -> Empty),
  sine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)) -> Empty)) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, Symmetry.quadrant_by(~F, ~field, square, cosine_sign, sine_sign))),
    A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, Symmetry.quadrant_by(~F, ~field, square, cosine_sign, sine_sign)))>:
  match square cosine_sign sine_sign:
    case P.Square{center, P.Frame{+cosine, +sine, +unit_below, +unit_above}} Inl{+cosine_up} Inl{+sine_up}:
      C.Both{cosine_up, sine_up}
    case P.Square{center, P.Frame{+cosine, +sine, +unit_below, +unit_above}} Inl{+cosine_up} Inr{sine_down}:
      C.Both{Symmetry.nonpositive(~F, ~field, sine, sine_down), cosine_up}
    case P.Square{center, P.Frame{+cosine, +sine, +unit_below, +unit_above}} Inr{cosine_down} Inl{+sine_up}:
      C.Both{Symmetry.double_negation(~F, ~field, sine, sine_up), Symmetry.nonpositive(~F, ~field, cosine, cosine_down)}
    case P.Square{center, P.Frame{+cosine, +sine, +unit_below, +unit_above}} Inr{cosine_down} Inr{sine_down}:
      C.Both{Symmetry.nonpositive(~F, ~field, cosine, cosine_down), Symmetry.nonpositive(~F, ~field, sine, sine_down)}

def Symmetry.first_quadrant_signs(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>) ->
  C.Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, Symmetry.first_quadrant(~F, ~field, square))),
    A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, Symmetry.first_quadrant(~F, ~field, square)))>:
  Symmetry.quadrant_signs(~F, ~field, square,
    K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)))

def Symmetry.quadrant_contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  cosine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)) -> Empty),
  sine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)) -> Empty),
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.quadrant_by(~F, ~field, square, cosine_sign, sine_sign), point>:
  match cosine_sign sine_sign:
    case Inl{a} Inl{b}:
      inside
    case Inl{a} Inr{b}:
      Symmetry.turn_contains(~F, ~field, square, point, inside)
    case Inr{a} Inl{b}:
      Symmetry.turn_contains(~F, ~field, Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, square)), point,
        Symmetry.turn_contains(~F, ~field, Symmetry.turn(~F, ~field, square), point, Symmetry.turn_contains(~F, ~field, square, point, inside)))
    case Inr{a} Inr{b}:
      Symmetry.turn_contains(~F, ~field, Symmetry.turn(~F, ~field, square), point, Symmetry.turn_contains(~F, ~field, square, point, inside))

def Symmetry.quadrant_contains_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  cosine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)) -> Empty),
  sine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)) -> Empty),
  inside: P.Problem.Containment<F, field, Symmetry.quadrant_by(~F, ~field, square, cosine_sign, sine_sign), point>) ->
  P.Problem.Containment<F, field, square, point>:
  match cosine_sign sine_sign:
    case Inl{a} Inl{b}:
      inside
    case Inl{a} Inr{b}:
      Symmetry.turn_contains_back(~F, ~field, square, point, inside)
    case Inr{a} Inl{b}:
      Symmetry.turn_contains_back(~F, ~field, square, point,
        Symmetry.turn_contains_back(~F, ~field, Symmetry.turn(~F, ~field, square), point,
          Symmetry.turn_contains_back(~F, ~field, Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, square)), point, inside)))
    case Inr{a} Inr{b}:
      Symmetry.turn_contains_back(~F, ~field, square, point, Symmetry.turn_contains_back(~F, ~field, Symmetry.turn(~F, ~field, square), point, inside))

def Symmetry.first_quadrant_contains(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, square, point>) ->
  P.Problem.Containment<F, field, Symmetry.first_quadrant(~F, ~field, square), point>:
  Symmetry.quadrant_contains(~F, ~field, square, point,
    K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), inside)

def Symmetry.first_quadrant_contains_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.Containment<F, field, Symmetry.first_quadrant(~F, ~field, square), point>) ->
  P.Problem.Containment<F, field, square, point>:
  Symmetry.quadrant_contains_back(~F, ~field, square, point,
    K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), inside)

def Symmetry.quadrant_interior_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  cosine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)) -> Empty),
  sine_sign: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)) -> Empty),
  inside: P.Problem.InteriorContainment<F, field, Symmetry.quadrant_by(~F, ~field, square, cosine_sign, sine_sign), point>) ->
  P.Problem.InteriorContainment<F, field, square, point>:
  match cosine_sign sine_sign:
    case Inl{a} Inl{b}:
      inside
    case Inl{a} Inr{b}:
      Symmetry.turn_interior_back(~F, ~field, square, point, inside)
    case Inr{a} Inl{b}:
      Symmetry.turn_interior_back(~F, ~field, square, point,
        Symmetry.turn_interior_back(~F, ~field, Symmetry.turn(~F, ~field, square), point,
          Symmetry.turn_interior_back(~F, ~field, Symmetry.turn(~F, ~field, Symmetry.turn(~F, ~field, square)), point, inside)))
    case Inr{a} Inr{b}:
      Symmetry.turn_interior_back(~F, ~field, square, point, Symmetry.turn_interior_back(~F, ~field, Symmetry.turn(~F, ~field, square), point, inside))

def Symmetry.first_quadrant_interior_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +point: P.Problem.Point<F>,
  inside: P.Problem.InteriorContainment<F, field, Symmetry.first_quadrant(~F, ~field, square), point>) ->
  P.Problem.InteriorContainment<F, field, square, point>:
  Symmetry.quadrant_interior_back(~F, ~field, square, point,
    K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.cosine(F, field, square)), K.Field.le_decidable(F, field)(A.Algebra.zero(~F, ~field), P.Problem.sine(F, field, square)), inside)

def Symmetry.first_quadrant_fits(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F, fits: Symmetry.Fits(~F, ~field, square, side)) ->
  Symmetry.Fits(~F, ~field, Symmetry.first_quadrant(~F, ~field, square), side):
  +point => inside => fits(point, Symmetry.first_quadrant_contains_back(~F, ~field, square, point, inside))

def Symmetry.first_quadrant_fits_back(~F: Kind(&2), ~field: K.Field<F>, +square: P.Problem.Square<F, field>, +side: F,
  fits: Symmetry.Fits(~F, ~field, Symmetry.first_quadrant(~F, ~field, square), side)) -> Symmetry.Fits(~F, ~field, square, side):
  +point => inside => fits(point, Symmetry.first_quadrant_contains(~F, ~field, square, point, inside))

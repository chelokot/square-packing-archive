use std::env;
use std::io::{self, Read};

const SCALE: i64 = 1_000_000_000_000;
const TIME_SCALE: i128 = 1_000_000_000_000_000;

#[derive(Clone, Copy, Debug)]
struct Atom {
    x: i64,
    y: i64,
    weight: i64,
}

#[derive(Clone, Copy)]
struct Bounds {
    scale: i64,
    cosine_low: i64,
    cosine_high: i64,
    sine_low: i64,
    sine_high: i64,
}

fn interval_products(
    first_low: i128,
    first_high: i128,
    second_low: i128,
    second_high: i128,
) -> (i128, i128) {
    let products = [
        first_low * second_low,
        first_low * second_high,
        first_high * second_low,
        first_high * second_high,
    ];
    (
        *products.iter().min().unwrap(),
        *products.iter().max().unwrap(),
    )
}

fn separated(u_low: i64, u_high: i64, v_low: i64, v_high: i64, bounds: Bounds) -> bool {
    let scale = i128::from(bounds.scale);
    let c_low = i128::from(bounds.cosine_low);
    let c_high = i128::from(bounds.cosine_high);
    let s_low = i128::from(bounds.sine_low);
    let s_high = i128::from(bounds.sine_high);
    let u_low = i128::from(u_low);
    let u_high = i128::from(u_high);
    let v_low = i128::from(v_low);
    let v_high = i128::from(v_high);
    let cosine_sine_low = c_low + s_low;
    let cosine_sine_high = c_high + s_high;
    let high_center = 128 * scale * scale - 8 * scale * cosine_sine_low;
    let u_minimum = 64 * cosine_sine_low;
    let u_maximum_scaled = 128 * scale * cosine_sine_high - 8 * cosine_sine_high * cosine_sine_low;
    let v_minimum_scaled =
        -128 * scale * s_high + 8 * s_high * cosine_sine_low + 64 * scale * c_low;
    let v_maximum_scaled =
        -64 * scale * s_low + 128 * scale * c_high - 8 * c_high * cosine_sine_low;
    if u_high <= u_minimum
        || scale * u_low >= u_maximum_scaled
        || scale * v_high <= v_minimum_scaled
        || scale * v_low >= v_maximum_scaled
    {
        return true;
    }
    let (sine_v_minimum, sine_v_maximum) = interval_products(s_low, s_high, v_low, v_high);
    let (cosine_v_minimum, cosine_v_maximum) = interval_products(c_low, c_high, v_low, v_high);
    let (cosine_u_minimum, cosine_u_maximum) = interval_products(c_low, c_high, u_low, u_high);
    let (sine_u_minimum, sine_u_maximum) = interval_products(s_low, s_high, u_low, u_high);
    let x_minimum = cosine_u_minimum - sine_v_maximum;
    let x_maximum = cosine_u_maximum - sine_v_minimum;
    let y_minimum = sine_u_minimum + cosine_v_minimum;
    let y_maximum = sine_u_maximum + cosine_v_maximum;
    let low_center = 64 * scale * scale;
    x_maximum <= low_center
        || x_minimum >= high_center
        || y_maximum <= low_center
        || y_minimum >= high_center
}

fn scan_edges<F>(
    x_edges: &[i64],
    y_edges: &[i64],
    rectangles: &[(i64, i64, i64, i64, i64)],
    denominator: i64,
    separated_run: F,
) -> Result<(usize, usize), String>
where
    F: Fn(usize, usize, usize, usize) -> bool,
{
    let ny = y_edges.len();
    let mut difference = vec![0i64; x_edges.len() * ny];
    for &(x_start, x_end, y_start, y_end, weight) in rectangles {
        let xl = x_edges.binary_search(&x_start).unwrap();
        let xh = x_edges.binary_search(&x_end).unwrap();
        let yl = y_edges.binary_search(&y_start).unwrap();
        let yh = y_edges.binary_search(&y_end).unwrap();
        difference[xl * ny + yl] += weight;
        difference[xh * ny + yl] -= weight;
        difference[xl * ny + yh] -= weight;
        difference[xh * ny + yh] += weight;
    }
    let mut columns = vec![0i64; ny];
    let mut bad_runs = 0usize;
    for row in 0..x_edges.len() - 1 {
        let mut score = 0i64;
        let mut run_start = None;
        for column in 0..ny - 1 {
            columns[column] += difference[row * ny + column];
            score += columns[column];
            if score < denominator {
                if run_start.is_none() {
                    run_start = Some(column);
                }
            } else if let Some(start) = run_start.take() {
                bad_runs += 1;
                if !separated_run(row, row + 1, start, column) {
                    return Err(format!(
                        "unresolved run u=({}, {}) v=({}, {}) score<{}",
                        x_edges[row],
                        x_edges[row + 1],
                        y_edges[start],
                        y_edges[column],
                        denominator
                    ));
                }
            }
        }
        if let Some(start) = run_start {
            bad_runs += 1;
            if !separated_run(row, row + 1, start, ny - 1) {
                return Err(format!(
                    "unresolved run u=({}, {}) v=({}, {}) score<{}",
                    x_edges[row],
                    x_edges[row + 1],
                    y_edges[start],
                    y_edges.last().unwrap(),
                    denominator
                ));
            }
        }
    }
    Ok((rectangles.len(), bad_runs))
}

#[derive(Clone, Copy, Debug)]
enum Edge {
    Constant(i64),
    Horizontal(Atom, i64),
    Vertical(Atom, i64),
}

impl Edge {
    fn range(self, bounds: Bounds) -> (i64, i64) {
        let scale = bounds.scale;
        match self {
            Edge::Constant(value) => (value * scale, value * scale),
            Edge::Horizontal(atom, shift) => (
                bounds.cosine_low * atom.x + bounds.sine_low * atom.y + shift * 8 * scale,
                bounds.cosine_high * atom.x + bounds.sine_high * atom.y + shift * 8 * scale,
            ),
            Edge::Vertical(atom, shift) => (
                -bounds.sine_high * atom.x + bounds.cosine_low * atom.y + shift * 8 * scale,
                -bounds.sine_low * atom.x + bounds.cosine_high * atom.y + shift * 8 * scale,
            ),
        }
    }

    fn polynomial(self) -> [i128; 5] {
        let d = [1, 0, 1, 0, 0];
        let c = [1, 0, -1, 0, 0];
        let s = [0, 2, 0, 0, 0];
        match self {
            Edge::Constant(value) => polynomial_scale(d, i128::from(value)),
            Edge::Horizontal(atom, shift) => polynomial_add(
                polynomial_add(
                    polynomial_scale(c, i128::from(atom.x)),
                    polynomial_scale(s, i128::from(atom.y)),
                ),
                polynomial_scale(d, i128::from(shift * 8)),
            ),
            Edge::Vertical(atom, shift) => polynomial_add(
                polynomial_sub(
                    polynomial_scale(c, i128::from(atom.y)),
                    polynomial_scale(s, i128::from(atom.x)),
                ),
                polynomial_scale(d, i128::from(shift * 8)),
            ),
        }
    }
}

fn polynomial_add(left: [i128; 5], right: [i128; 5]) -> [i128; 5] {
    std::array::from_fn(|index| left[index] + right[index])
}

fn polynomial_sub(left: [i128; 5], right: [i128; 5]) -> [i128; 5] {
    std::array::from_fn(|index| left[index] - right[index])
}

fn polynomial_scale(value: [i128; 5], factor: i128) -> [i128; 5] {
    value.map(|coefficient| coefficient * factor)
}

fn polynomial_product(left: [i128; 5], right: [i128; 5]) -> [i128; 5] {
    let mut product = [0; 5];
    for first in 0..5 {
        for second in 0..5 - first {
            product[first + second] += left[first] * right[second];
        }
    }
    product
}

fn separator_polynomials(
    x_left: Edge,
    x_right: Edge,
    y_bottom: Edge,
    y_top: Edge,
) -> [[i128; 5]; 8] {
    let d = [1, 0, 1, 0, 0];
    let c = [1, 0, -1, 0, 0];
    let s = [0, 2, 0, 0, 0];
    let sum = polynomial_add(c, s);
    let left = x_left.polynomial();
    let right = x_right.polynomial();
    let bottom = y_bottom.polynomial();
    let top = y_top.polynomial();
    let d_squared = polynomial_product(d, d);
    let d_sum = polynomial_product(d, sum);
    [
        polynomial_sub(polynomial_scale(sum, 64), right),
        polynomial_add(
            polynomial_sub(polynomial_product(d, left), polynomial_scale(d_sum, 128)),
            polynomial_scale(polynomial_product(sum, sum), 8),
        ),
        polynomial_sub(
            polynomial_add(
                polynomial_sub(
                    polynomial_scale(polynomial_product(d, c), 64),
                    polynomial_scale(polynomial_product(d, s), 128),
                ),
                polynomial_scale(polynomial_product(s, sum), 8),
            ),
            polynomial_product(d, top),
        ),
        polynomial_add(
            polynomial_sub(
                polynomial_add(
                    polynomial_product(d, bottom),
                    polynomial_scale(polynomial_product(d, s), 64),
                ),
                polynomial_scale(polynomial_product(d, c), 128),
            ),
            polynomial_scale(polynomial_product(c, sum), 8),
        ),
        polynomial_add(
            polynomial_sub(
                polynomial_scale(d_squared, 64),
                polynomial_product(c, right),
            ),
            polynomial_product(s, bottom),
        ),
        polynomial_add(
            polynomial_sub(polynomial_product(c, left), polynomial_product(s, top)),
            polynomial_sub(polynomial_scale(d_sum, 8), polynomial_scale(d_squared, 128)),
        ),
        polynomial_sub(
            polynomial_sub(
                polynomial_scale(d_squared, 64),
                polynomial_product(s, right),
            ),
            polynomial_product(c, top),
        ),
        polynomial_add(
            polynomial_add(polynomial_product(s, left), polynomial_product(c, bottom)),
            polynomial_sub(polynomial_scale(d_sum, 8), polynomial_scale(d_squared, 128)),
        ),
    ]
}

fn polynomial_positive(polynomial: [i128; 5], time_low: i64, time_high: i64) -> bool {
    let first = polynomial.iter().position(|coefficient| *coefficient != 0);
    let last = polynomial.iter().rposition(|coefficient| *coefficient != 0);
    let (Some(first), Some(last)) = (first, last) else {
        return false;
    };
    let value_scale = TIME_SCALE;
    let mut lower = polynomial[last] * value_scale;
    let mut upper = lower;
    for index in (first..last).rev() {
        let products = [
            lower * i128::from(time_low),
            lower * i128::from(time_high),
            upper * i128::from(time_low),
            upper * i128::from(time_high),
        ];
        lower =
            products.iter().min().unwrap().div_euclid(TIME_SCALE) + polynomial[index] * value_scale;
        let maximum = *products.iter().max().unwrap();
        let quotient = maximum.div_euclid(TIME_SCALE);
        let remainder = maximum.rem_euclid(TIME_SCALE);
        upper = quotient + i128::from(remainder != 0) + polynomial[index] * value_scale;
    }
    lower > 0
}

fn ordered_edges(mut pairs: Vec<(i64, Edge)>) -> Result<(Vec<i64>, Vec<Edge>), String> {
    pairs.sort_unstable_by_key(|entry| entry.0);
    if pairs.windows(2).any(|window| window[0].0 == window[1].0) {
        return Err("sample lies on an arrangement event".to_string());
    }
    let values = pairs.iter().map(|entry| entry.0).collect();
    let sources = pairs.into_iter().map(|entry| entry.1).collect();
    Ok((values, sources))
}

fn verify_moving(
    atoms: &[Atom],
    denominator: i64,
    sample: Bounds,
    interval: Bounds,
    time: (i64, i64),
) -> Result<(usize, usize), String> {
    let scale = sample.scale;
    let mut horizontal = vec![
        (-256 * scale, Edge::Constant(-256)),
        (256 * scale, Edge::Constant(256)),
    ];
    let mut vertical = vec![
        (-256 * scale, Edge::Constant(-256)),
        (256 * scale, Edge::Constant(256)),
    ];
    let mut rectangles = Vec::with_capacity(atoms.len());
    for &atom in atoms {
        if atom.x < 53 || atom.y < 53 {
            continue;
        }
        let projected_x = sample.cosine_low * atom.x + sample.sine_low * atom.y;
        let projected_y = -sample.sine_low * atom.x + sample.cosine_low * atom.y;
        let x_start = projected_x - 8 * scale;
        let x_end = projected_x + 8 * scale;
        let y_start = projected_y - 8 * scale;
        let y_end = projected_y + 8 * scale;
        rectangles.push((x_start, x_end, y_start, y_end, atom.weight));
        horizontal.push((x_start, Edge::Horizontal(atom, -1)));
        horizontal.push((x_end, Edge::Horizontal(atom, 1)));
        vertical.push((y_start, Edge::Vertical(atom, -1)));
        vertical.push((y_end, Edge::Vertical(atom, 1)));
    }
    let (x_edges, x_sources) = ordered_edges(horizontal)?;
    let (y_edges, y_sources) = ordered_edges(vertical)?;
    let debug = env::var_os("DEBUG_MOVING").is_some();
    scan_edges(
        &x_edges,
        &y_edges,
        &rectangles,
        denominator,
        |xl, xh, yl, yh| {
            let u_low = x_sources[xl].range(interval).0;
            let u_high = x_sources[xh].range(interval).1;
            let v_low = y_sources[yl].range(interval).0;
            let v_high = y_sources[yh].range(interval).1;
            let interval_separated = separated(u_low, u_high, v_low, v_high, interval);
            let polynomial_separated = if interval_separated {
                false
            } else {
                separator_polynomials(x_sources[xl], x_sources[xh], y_sources[yl], y_sources[yh])
                    .into_iter()
                    .any(|polynomial| polynomial_positive(polynomial, time.0, time.1))
            };
            let result = interval_separated || polynomial_separated;
            if debug && !result {
                eprintln!(
                    "sources {:?} {:?} {:?} {:?}",
                    x_sources[xl], x_sources[xh], y_sources[yl], y_sources[yh]
                );
            }
            result
        },
    )
}

fn exact_point_bounds(numerator: i128, denominator: i128) -> Bounds {
    let squared_numerator = numerator * numerator;
    let squared_denominator = denominator * denominator;
    let scale: i64 = (squared_numerator + squared_denominator)
        .try_into()
        .unwrap();
    let cosine: i64 = (squared_denominator - squared_numerator)
        .try_into()
        .unwrap();
    let sine: i64 = (2 * numerator * denominator).try_into().unwrap();
    Bounds {
        scale,
        cosine_low: cosine,
        cosine_high: cosine,
        sine_low: sine,
        sine_high: sine,
    }
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    assert_eq!(arguments.len(), 2);
    assert_eq!(arguments[1], "cells");
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut fields = input.split_whitespace();
    let denominator: i64 = fields.next().unwrap().parse().unwrap();
    let atom_count: usize = fields.next().unwrap().parse().unwrap();
    let mass: i64 = fields.next().unwrap().parse().unwrap();
    assert!(mass < 61 * denominator);
    let atoms: Vec<Atom> = (0..atom_count)
        .map(|_| Atom {
            x: fields.next().unwrap().parse().unwrap(),
            y: fields.next().unwrap().parse().unwrap(),
            weight: fields.next().unwrap().parse().unwrap(),
        })
        .collect();
    assert_eq!(mass, atoms.iter().map(|atom| atom.weight).sum::<i64>());
    let cell_count: usize = fields.next().unwrap().parse().unwrap();
    assert_eq!(cell_count, 6_871);
    let mut total_runs = 0usize;
    for index in 0..cell_count {
        let numerator: i128 = fields.next().unwrap().parse().unwrap();
        let denominator_angle: i128 = fields.next().unwrap().parse().unwrap();
        let cosine_low: i64 = fields.next().unwrap().parse().unwrap();
        let cosine_high: i64 = fields.next().unwrap().parse().unwrap();
        let sine_low: i64 = fields.next().unwrap().parse().unwrap();
        let sine_high: i64 = fields.next().unwrap().parse().unwrap();
        let time_low: i64 = fields.next().unwrap().parse().unwrap();
        let time_high: i64 = fields.next().unwrap().parse().unwrap();
        let sample = exact_point_bounds(numerator, denominator_angle);
        let interval = Bounds {
            scale: SCALE,
            cosine_low,
            cosine_high,
            sine_low,
            sine_high,
        };
        match verify_moving(&atoms, denominator, sample, interval, (time_low, time_high)) {
            Ok((_, runs)) => total_runs += runs,
            Err(problem) => {
                eprintln!("cell={index} t={numerator}/{denominator_angle} {problem}");
                std::process::exit(1);
            }
        }
        if index % 500 == 0 {
            eprintln!("cells_checked={}", index + 1);
        }
    }
    assert!(fields.next().is_none());
    println!("verified_cells={cell_count} failures=0 total_runs={total_runs}");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluate(polynomial: [i128; 5], numerator: i128, denominator: i128) -> i128 {
        polynomial
            .iter()
            .enumerate()
            .map(|(degree, coefficient)| {
                coefficient * numerator.pow(degree as u32) * denominator.pow((4 - degree) as u32)
            })
            .sum()
    }

    #[test]
    fn boundary_separator_polynomial() {
        let right = Edge::Horizontal(
            Atom {
                x: 72,
                y: 54,
                weight: 1,
            },
            -1,
        );
        let bottom = Edge::Vertical(
            Atom {
                x: 69,
                y: 112,
                weight: 1,
            },
            1,
        );
        let polynomials =
            separator_polynomials(Edge::Constant(-256), right, bottom, Edge::Constant(256));
        assert_eq!(polynomials[4], [0, 132, -4, -100, -16]);
        assert!(polynomial_positive(polynomials[4], 0, 6_747_000_000_000));
    }

    #[test]
    fn separator_polynomials_keep_feasible_centers() {
        let denominator = 100i128;
        for numerator in 0..=41i128 {
            let divisor = denominator * denominator + numerator * numerator;
            let cosine = denominator * denominator - numerator * numerator;
            let sine = 2 * numerator * denominator;
            let u = 64 * (cosine + sine);
            let v = 64 * (cosine - sine);
            let left = u.div_euclid(divisor) - 1;
            let right = -(-u).div_euclid(divisor) + 1;
            let bottom = v.div_euclid(divisor) - 1;
            let top = -(-v).div_euclid(divisor) + 1;
            let polynomials = separator_polynomials(
                Edge::Constant(left as i64),
                Edge::Constant(right as i64),
                Edge::Constant(bottom as i64),
                Edge::Constant(top as i64),
            );
            for polynomial in polynomials {
                assert!(evaluate(polynomial, numerator, denominator) <= 0);
            }
        }
    }

    #[test]
    fn positive_interval_bounds_are_sound_on_test_grid() {
        let mut seed = 37u64;
        for index in 0..400 {
            let mut polynomial = [0i128; 5];
            for coefficient in &mut polynomial {
                seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                *coefficient = i128::from((seed >> 32) % 41) - 20;
            }
            let left = i128::from(index) * TIME_SCALE / 1000;
            let right = i128::from(index + 1) * TIME_SCALE / 1000;
            if polynomial_positive(polynomial, left as i64, right as i64) {
                assert!(evaluate(polynomial, i128::from(index) * 2 + 1, 2000) > 0);
            }
        }
    }

    #[test]
    fn interval_separation_keeps_known_feasible_centers() {
        for index in 0..1000i64 {
            let numerator = index % 40;
            let denominator = 100;
            let d = denominator * denominator + numerator * numerator;
            let c = denominator * denominator - numerator * numerator;
            let s = 2 * numerator * denominator;
            let center_x = 4 + index % 4;
            let center_y = 4 + (index / 4) % 4;
            let u = 16 * (c * center_x + s * center_y);
            let v = 16 * (-s * center_x + c * center_y);
            let bounds = Bounds {
                scale: d,
                cosine_low: c - 1,
                cosine_high: c + 1,
                sine_low: (s - 1).max(0),
                sine_high: s + 1,
            };
            let u_low = if index % 2 == 0 { -256 * d } else { u - d };
            let v_low = if index % 3 == 0 { -256 * d } else { v - d };
            assert!(!separated(u_low, u + d, v_low, v + d, bounds));
        }
    }
}

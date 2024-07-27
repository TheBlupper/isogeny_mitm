#![feature(test)]
#![feature(const_option)]
#![allow(non_snake_case)]

extern crate test;

use ark_ff::fields::*;
use ark_ff::BigInt;
use ark_ff::BigInteger;
use ark_std::UniformRand;

use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt;
use std::str::FromStr;

use lazy_static::lazy_static;

// CHANGING CONFIG:
// - Change "modulus = ..." below to the the prime p you want to use
// - Change "generator = ..." to a multiplicative generator of GF(p)
// - Change "Fp128<MontBackend<FqConfig, ...>>" to ceil(p.nbits() / 64)
// - Change NONRESIDUE below to a quadratic nonresidue in Fq. This will
// be r when constructing the extension GF(p**2) with modulus (x**2 - r)
// - Change S below to (p**2 - 1) / 2. Make sure to adjust
// the size of the BigInt if needed

#[derive(MontConfig)]
#[modulus = "20628849596981071092343898111"]
#[generator = "7"]
struct FqConfig;
type Fq = Fp128<MontBackend<FqConfig, 2>>;

const NONRESIDUE: Fq = MontFp!("-1");

type Fq2Exponent = BigInt<3>;
const S: Fq2Exponent = BigInt!("212774717847433049615426951484283937883354640167374684160");

// END CONFIG

type Fq2 = Fp2<Fq2Config>;
struct Fq2Config;

// Boilerplate copied from
impl Fp2Config for Fq2Config {
    type Fp = Fq;

    #[rustfmt::skip]
    const NONRESIDUE: Fq = NONRESIDUE;

    // This is not used by this program but needs to be initilized
    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP2_C1: &'static [Fq] = &[
        MontFp!("1337"),
        MontFp!("1337"),
    ];
}

// Constants used throughout the program
// Precomputing provides a small speedup
// mainly for two_isogenies_from_prev
lazy_static! {
    static ref CONST_INV_2: Fq2 = Fq2::new(MontFp!("2"), MontFp!("0")).inverse().unwrap();
}
static CONST_4: Fq2 = Fq2::new(MontFp!("4"), MontFp!("0"));
static CONST_1488: Fq2 = Fq2::new(MontFp!("1488"), MontFp!("0"));
static CONST_162000: Fq2 = Fq2::new(MontFp!("162000"), MontFp!("0"));
static CONST_40773375: Fq2 = Fq2::new(MontFp!("40773375"), MontFp!("0"));
static CONST_8748000000: Fq2 = Fq2::new(MontFp!("8748000000"), MontFp!("0"));
static CONST_157464000000000: Fq2 = Fq2::new(MontFp!("157464000000000"), MontFp!("0"));

#[derive(Clone, Debug)]
struct QuadraticPolyFp2 {
    // represents ax^2 + bx + c
    a: Fq2,
    b: Fq2,
    c: Fq2,
}

impl QuadraticPolyFp2 {
    fn new(a: Fq2, b: Fq2, c: Fq2) -> QuadraticPolyFp2 {
        Self { a, b, c }
    }

    fn mul_mod(&self, other: &QuadraticPolyFp2, modulus: &MonicCubicPolyFp2) -> QuadraticPolyFp2 {
        let x4 = self.a * other.a;
        let mut x3 = self.b * other.a + self.a * other.b;
        let mut x2 = self.c * other.a + self.b * other.b + self.a * other.c;
        let mut x1 = self.c * other.b + self.b * other.c;
        let mut x0 = self.c * other.c;

        x3 -= x4 * modulus.b;
        x2 -= x4 * modulus.c;
        x1 -= x4 * modulus.d;

        x2 -= x3 * modulus.b;
        x1 -= x3 * modulus.c;
        x0 -= x3 * modulus.d;

        QuadraticPolyFp2::new(x2, x1, x0)
    }

    fn pow_mod(self, exp: Fq2Exponent, modulus: &MonicCubicPolyFp2) -> QuadraticPolyFp2 {
        let mut res = QuadraticPolyFp2::new(Fq2::ZERO, Fq2::ZERO, Fq2::ONE);
        let mut curr = self;
        let mut curr_exp = exp;
        while !curr_exp.is_zero() {
            if curr_exp.is_odd() {
                res = res.mul_mod(&curr, modulus);
            }
            curr = curr.mul_mod(&curr, modulus);
            curr_exp.div2();
        }
        res
    }

    fn roots(&self) -> Vec<Fq2> {
        if self.a == Fq2::ZERO {
            if self.b == Fq2::ZERO {
                return vec![];
            }
            return vec![-self.c / self.b];
        }

        let disc2 = self.b.square() - Fq2::from(4) * self.c;
        match disc2.sqrt() {
            None => vec![],
            Some(disc) => vec![
                (-self.b + disc) / Fq2::from(2),
                (-self.b - disc) / Fq2::from(2),
            ],
        }
    }

    fn degree(&self) -> u64 {
        if self.a == Fq2::ZERO {
            if self.b == Fq2::ZERO {
                return 0;
            }
            return 1;
        }
        return 2;
    }

    fn is_zero(&self) -> bool {
        self.a == Fq2::ZERO && self.b == Fq2::ZERO && self.c == Fq2::ZERO
    }

    fn common_root(&self, other: &QuadraticPolyFp2) -> Option<Fq2> {
        if self.degree() != 2 || other.degree() != 2 {
            return None; // can't be bothered
        }

        let resultant = self.c.square() * other.a.square() - self.b * self.c * other.a * other.b
            + self.a * self.c * other.b.square()
            + self.b.square() * other.a * other.c
            - self.a.double() * self.c * other.a * other.c
            - self.a * self.b * other.b * other.c
            + self.a.square() * other.c.square();

        if resultant != Fq2::ZERO {
            return None;
        }

        let selfinv = self.a.inverse().unwrap();
        let otherinv = other.a.inverse().unwrap();
        let num = other.c * otherinv - self.c * selfinv;
        let denom = self.b * selfinv - other.b * otherinv;
        match denom.inverse() {
            None => return None,
            Some(denominv) => return Some(num * denominv),
        }
    }
}

impl fmt::Display for QuadraticPolyFp2 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({})*x^2 + ({})*x + {}",
            &fmt_fq2(&self.a),
            &fmt_fq2(&self.b),
            &fmt_fq2(&self.c)
        )
    }
}

// This is used for computing the initial roots of the cubic modular polynomial
#[derive(Debug)]
struct MonicCubicPolyFp2 {
    // represents x^3 + bx^2 + cx + d
    b: Fq2,
    c: Fq2,
    d: Fq2,
}

// This whole impl is not optimized for speed, it's only used twice in the start
impl MonicCubicPolyFp2 {
    fn new(b: Fq2, c: Fq2, d: Fq2) -> MonicCubicPolyFp2 {
        Self { b, c, d }
    }

    fn common_root(&self, other: &QuadraticPolyFp2) -> Option<Fq2> {
        match other.a.inverse() {
            // fails if a == 0
            None => None, // could handle this but, eh...
            Some(a_inv) => {
                return QuadraticPolyFp2::new(
                    self.b - other.b * a_inv,
                    self.c - other.c * a_inv,
                    self.d,
                )
                .common_root(other);
            }
        }
    }

    // this is only run in the start so it's not optimized for speed
    fn roots(&self) -> Vec<Fq2> {
        if self.d == Fq2::ZERO {
            let mut roots = QuadraticPolyFp2::new(Fq2::ONE, self.b, self.c).roots();
            roots.push(Fq2::ZERO);
            return roots;
        }

        // resultant of f and f'', is 0 iff f has a triple root
        let res_triple = -Fq2::from(16) * self.b.square() * self.b
            + Fq2::from(72) * self.b * self.c
            - Fq2::from(216) * self.d;

        if res_triple == Fq2::ZERO {
            let r = -self.b / Fq2::from(3);
            return vec![r];
        }

        // resultant of f and f', is 0 iff f has a double root
        let res_dbl = -self.b.square() * self.c.square()
            + Fq2::from(4) * self.c.square() * self.c
            + Fq2::from(4) * self.b.square() * self.b * self.d
            - Fq2::from(18) * self.b * self.c * self.d
            + Fq2::from(27) * self.d.square();

        if res_dbl == Fq2::ZERO {
            // f has a double root
            // https://qr.ae/p2XSb6

            let disc = Fq2::from(3) * self.c - self.b.square();
            assert!(disc != Fq2::ZERO);

            let r = (self.b * self.c - Fq2::from(9) * self.d) / (Fq2::from(2) * disc);
            let s = (self.b * self.b.square() + Fq2::from(9) * self.d
                - Fq2::from(4) * self.b * self.c)
                / disc;
            return vec![r, s];
        }

        let mut q = S.clone();
        q.mul2();
        q.add_with_carry(&Fq2Exponent::one()); // p^2

        let mut full_poly = QuadraticPolyFp2::new(Fq2::ZERO, Fq2::ONE, Fq2::ZERO);
        full_poly = full_poly.pow_mod(q, &self);
        full_poly.b -= Fq2::ONE; // x^(p^2) - x, has all elements of GF(p) as roots

        if !full_poly.is_zero() {
            match self.common_root(&full_poly) {
                None => return vec![],
                Some(common_root) => return self.all_roots(&common_root),
            }
        }

        // Cantor-Zassenhaus
        let mut rng = rand::thread_rng();
        let root;
        loop {
            // in my testing this never hangs, lmk if it does for you
            let delta = Fq2::rand(&mut rng);

            // x + delta
            let mut g = QuadraticPolyFp2::new(Fq2::ZERO, Fq2::ONE, delta);
            g = g.pow_mod(S, &self);
            g.c -= Fq2::ONE;

            // (x + delta)^s - 1 mod self
            match self.common_root(&g) {
                None => continue,
                Some(common_root) => {
                    root = common_root;
                    break;
                }
            }
        }

        self.all_roots(&root)
    }

    // finds the remaining roots given one root
    fn all_roots(&self, root: &Fq2) -> Vec<Fq2> {
        let mut roots = QuadraticPolyFp2::new(
            Fq2::ONE,
            self.b + root,
            self.b * root + root.square() + self.c,
        )
        .roots();
        roots.push(*root);
        roots
    }
}

impl fmt::Display for MonicCubicPolyFp2 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "x^3 + ({})*x^2 + ({})*x + {}",
            &fmt_fq2(&self.b),
            &fmt_fq2(&self.c),
            &fmt_fq2(&self.d)
        )
    }
}

#[derive(Clone)]
struct WeierstrassCurve {
    a: Fq2,
    b: Fq2,
}

impl WeierstrassCurve {
    fn new(a: Fq2, b: Fq2) -> WeierstrassCurve {
        Self { a, b }
    }

    // 2-division polynomial
    fn division_poly_2(&self) -> MonicCubicPolyFp2 {
        MonicCubicPolyFp2::new(Fq2::ZERO, self.a, self.b)
    }

    fn j_invariant(&self) -> Fq2 {
        let a3 = self.a.square() * self.a;
        let b2 = self.b.square();
        let num = Fq2::from(1728 * 4) * a3;
        let denom = Fq2::from(4) * a3 + Fq2::from(27) * b2;
        num / denom
    }

    // finds a corresponding y-coordinate for a given x-coordinate
    fn calc_y(&self, x: Fq2) -> Option<Fq2> {
        let rhs = x.square() * x + self.a * x + self.b;
        match rhs.sqrt() {
            Some(y) => Some(y),
            None => None,
        }
    }
}

// v and x0 are used for Kohel's formula.
// The map of the x-coordinate will be phi(x) = (x^2 - x0*x + v) / (x - x0)
struct Isogeny2 {
    v: Fq2,
    x0: Fq2,
    domain: WeierstrassCurve,
    // codomain not needed
}

impl Isogeny2 {
    fn new(v: Fq2, x0: Fq2, domain: WeierstrassCurve) -> Isogeny2 {
        Self { v, x0, domain }
    }

    #[allow(dead_code)]
    fn image(&self, x: Fq2) -> Fq2 {
        (x.square() - self.x0 * x + self.v) / (x - self.x0)
    }

    fn preimages(&self, x: Fq2) -> Vec<Fq2> {
        QuadraticPolyFp2::new(Fq2::ONE, -self.x0 - x, self.v + x * self.x0).roots()
    }
}

#[allow(dead_code)]
fn modular_poly_2(X: Fq2, Y: Fq2) -> Fq2 {
    let X2 = X.square();
    let Y2 = Y.square();
    let XY = X * Y;
    X2 * X + Y2 * Y - XY.square()
        + CONST_1488 * (X2 * Y + X * Y2)
        + CONST_162000 * (-X2 - Y2)
        + CONST_40773375 * XY
        + CONST_8748000000 * (X + Y)
        - CONST_157464000000000
}

// returns all neighbouring 2-isogenies by solving a cubic
fn two_isogenies(j: &Fq2) -> Vec<Fq2> {
    let j2 = j.square();
    MonicCubicPolyFp2::new(
        -j2 + CONST_1488 * j - CONST_162000,
        CONST_1488 * j2 + CONST_40773375 * j + CONST_8748000000,
        j2 * j - CONST_162000 * j2 + CONST_8748000000 * j - CONST_157464000000000,
    )
    .roots()
}

/**
This is an explanation of `two_isogenies_from_prev`

Two curves are 2-isogenous if their respective j-invariants (j0, j1) together form a root of the following polynomial:
M(X, Y) = X^3 - X^2*Y^2 + 1488*X^2*Y - 162000*X^2 + 1488*X*Y^2 + 40773375*X*Y + 8748000000*X + Y^3 - 162000*Y^2 + 8748000000*Y - 157464000000000

The current j-invariant is jc and the previous j-invariant was jp. That means that (jc, jp) is a root of M.
We are interested in the other two solutions of M(x, jc) = 0, where x is the new j-invariant. I.e roots of

f(x) = x^3 + (-jc^2 + 1488*jc - 162000)*x^2 + (1488*jc^2 + 40773375*jc + 8748000000)*x + (jc^3 - 162000*jc^2 + 8748000000*jc - 157464000000000)

For a monic cubic x^3 + bx^2 + cx + d with the roots r1, r2 and r3 we have by Vieta's formulas:
r1+r2+r3 = -b
r1*r2 + r1*r3 + r2*r3 = c
r1*r2*r3 = -d

We set r3=jp and obtain
r1+r2 = -b - jp
r1*r2 = c - (r1 + r2)*jp = (b + jp)*jp + c = jp^2 + b*jp + c
(last equation not needed)

Knowing the sum and product of r1 and r2 means they are the solutions of the quadratic
x^2 + (b + jp)*x + (jp^2 + b*jp + c)
(also by Vieta)

Expanding b and c from our original cubic we get

x^2 + (-jc^2 + 1488*jc + jp - 162000)*x + (jp^2 - jc^2*jp + 1488*(jc^2 + jc*jp) + 40773375*jc - 162000*jp + 8748000000)

This is a quadratic we can easily solve for roots of
**/
fn two_isogenies_from_prev(jc: &Fq2, jp: &Fq2) -> Result<(Fq2, Fq2), ()> {
    let jc2 = jc.square();
    let b = -jc2 + CONST_1488 * jc + jp - CONST_162000;
    let c = jp.square() - jc2 * jp + CONST_1488 * (jc2 + jc * jp) + CONST_40773375 * jc
        - CONST_162000 * jp
        + CONST_8748000000;

    // now we solve the quadratic x^2 + b*x + c
    let d2 = b.square() - CONST_4 * c;
    match d2.sqrt() {
        None => Err(()),
        Some(d) => Ok(((-b + d) * *CONST_INV_2, (-b - d) * *CONST_INV_2)),
    }
}

fn find_isogeny_path(j_start: Fq2, j_target: Fq2, exp: u64) -> Option<Vec<Fq2>> {
    let j_starts = two_isogenies(&j_start);
    let j_targets = two_isogenies(&j_target);

    let exp_2 = (exp - 2) / 2;
    let exp_1 = (exp - 2) - exp_2;

    // splitting this up into levels provide negligible speedups and clutters the code
    let mut parents: HashMap<Fq2, Fq2> = HashMap::new();
    let mut parents2: HashMap<Fq2, Fq2> = HashMap::new();

    j_starts.iter().for_each(|j| {
        parents.insert(j.clone(), j_start);
    });

    j_targets.iter().for_each(|j| {
        parents2.insert(j.clone(), j_target);
    });

    let mut queue = VecDeque::from_iter(j_starts.iter().map(|j| (j.clone(), 0)));

    while !queue.is_empty() {
        let (j, depth) = queue.pop_back().unwrap();
        if depth >= exp_1 {
            continue;
        }
        let (j1, j2) = two_isogenies_from_prev(&j, parents.get(&j).unwrap())
            .expect("Failed to compute neighboring curves, are your j-invariants supersingular?");

        for j_new in vec![j1, j2] {
            if parents.contains_key(&j_new) {
                continue;
            }
            parents.insert(j_new.clone(), j);
            queue.push_back((j_new.clone(), depth + 1));
        }
    }

    println!("Computed lookup table (halfway there)");

    queue.clear();
    queue.extend(j_targets.iter().map(|j| (j.clone(), 0)));
    while !queue.is_empty() {
        let (j, depth) = queue.pop_back().unwrap();
        if depth >= exp_2 {
            continue;
        }

        let (j1, j2) = two_isogenies_from_prev(&j, parents2.get(&j).unwrap())
            .expect("Failed to compute neighboring curves, are your j-invariants supersingular?");

        for j_new in vec![j1, j2] {
            if !parents2.contains_key(&j_new) {
                parents2.insert(j_new.clone(), j);
                queue.push_back((j_new.clone(), depth + 1));
            }

            if parents.contains_key(&j_new) {
                // we found it! now just construct the path we used to get here
                // the path will include both the starting and ending curve
                let mut path = vec![];
                let mut j_curr = &j_new;
                loop {
                    path.push(j_curr.clone());
                    if j_curr == &j_start {
                        break;
                    };
                    j_curr = parents.get(j_curr).unwrap();
                }
                path.reverse();

                j_curr = &j_new;
                loop {
                    j_curr = parents2.get(j_curr).unwrap();
                    path.push(j_curr.clone());
                    if j_curr == &j_target {
                        break;
                    };
                }
                return Some(path);
            }
        }
    }
    return None;
}

// accepts a weierstrass curve and a path of j-invariants and computes
// a generator point of the kernel of the full isogeny chain (up to isomorphism)
fn compute_kernel(E0: &WeierstrassCurve, j_invs: &Vec<Fq2>) -> Result<(Fq2, Fq2), ()> {
    let mut phis: Vec<Isogeny2> = Vec::new();
    let mut E_curr = E0.clone();

    for j_inv in j_invs.iter().skip(1) {
        let mut found = false;
        for x0 in E_curr.division_poly_2().roots() {
            let v = Fq2::from(3) * x0.square() + E_curr.a;
            let w = x0 * v;

            let Enew =
                WeierstrassCurve::new(E_curr.a - Fq2::from(5) * v, E_curr.b - Fq2::from(7) * w);
            if Enew.j_invariant() == *j_inv {
                found = true;
                phis.push(Isogeny2::new(v, x0, E_curr));
                E_curr = Enew;
                break;
            }
        }

        if !found {
            return Err(());
        }
    }

    let mut x_gen = phis.last().unwrap().x0;
    let mut y_gen = Fq2::ZERO; // placeholder
    for phi in phis.iter().rev().skip(1) {
        let mut found = false;
        for x_new in phi.preimages(x_gen) {
            match phi.domain.calc_y(x_new) {
                None => continue,
                Some(y_new) => {
                    x_gen = x_new;
                    y_gen = y_new;
                    found = true;
                    break;
                }
            }
        }
        if !found {
            return Err(());
        }
    }

    Ok((x_gen, y_gen))
}

fn fmt_fq2(f: &Fq2) -> String {
    match (f.c0 == Fq::ZERO, f.c1 == Fq::ZERO) {
        (true, true) => "0".to_string(),
        (true, false) => format!("{}*i", f.c1),
        (false, true) => format!("{}", f.c0),
        (false, false) => format!("{} + {}*i", f.c0, f.c1),
    }
}

fn main() {
    if std::env::args().len() != 8 {
        println!(
            "Usage: {} E_a0 E_a1 E_b0 E_b1 j0 j1 deg_exp",
            std::env::args().nth(0).unwrap()
        );
        return;
    }

    let E_a0 = Fq::from_str(std::env::args().nth(1).unwrap().as_str()).expect("Invalid E_a0");
    let E_a1 = Fq::from_str(std::env::args().nth(2).unwrap().as_str()).expect("Invalid E_a1");
    let E_b0 = Fq::from_str(std::env::args().nth(3).unwrap().as_str()).expect("Invalid E_b0");
    let E_b1 = Fq::from_str(std::env::args().nth(4).unwrap().as_str()).expect("Invalid E_b1");
    let j_target0 = Fq::from_str(std::env::args().nth(5).unwrap().as_str()).expect("Invalid j0");
    let j_target1 = Fq::from_str(std::env::args().nth(6).unwrap().as_str()).expect("Invalid j1");
    let deg_exp = std::env::args()
        .nth(7)
        .unwrap()
        .parse::<u64>()
        .expect("Invalid deg_exp");

    let E_a = Fq2::new(E_a0, E_a1);
    let E_b = Fq2::new(E_b0, E_b1);
    let E = WeierstrassCurve::new(E_a, E_b);
    let j_start = E.j_invariant();
    let j_target = Fq2::new(j_target0, j_target1);

    match find_isogeny_path(j_start, j_target, deg_exp) {
        None => println!("No path found"),
        Some(path) => {
            println!("Found! Path of j-invariants:");
            for j in &path {
                println!("{}", fmt_fq2(j));
            }
            println!("--------------------------------");
            match compute_kernel(&E, &path) {
                Err(_) => println!("Failed to compute kernel"),
                Ok(K) => {
                    println!(
                        "Generator of kernel: ({}, {})",
                        fmt_fq2(&K.0),
                        fmt_fq2(&K.1)
                    );
                }
            }
        }
    }
}

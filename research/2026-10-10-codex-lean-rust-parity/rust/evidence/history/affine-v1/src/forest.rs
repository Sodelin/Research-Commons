//! Exact ordinary-population coordinate from the inherited hook-history and
//! root-count formula. No full forest law or source recognizer is constructed.
use crate::{q, Rational};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tree { Leaf(usize), Node(Box<Tree>, Box<Tree>) }
pub type Forest = Vec<Tree>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coordinate {
    pub roots: usize,
    pub mergers: usize,
    pub hook_product: BigInt,
    pub histories: BigInt,
    pub probability: Rational,
}

fn scan(tree: &Tree, m: usize, seen: &mut [bool], hooks: &mut BigInt)
    -> Result<(usize, usize), &'static str> {
    match tree {
        Tree::Leaf(label) => {
            if *label == 0 || *label > m || seen[*label - 1] { return Err("FOREST_LABELS"); }
            seen[*label - 1] = true;
            Ok((1, *label))
        }
        Tree::Node(a, b) => {
            let (sa, la) = scan(a, m, seen, hooks)?;
            let (sb, lb) = scan(b, m, seen, hooks)?;
            if la >= lb { return Err("FOREST_CANONICAL"); }
            *hooks *= BigInt::from(sa + sb - 1);
            Ok((sa + sb, la))
        }
    }
}

fn rate(j: usize) -> usize { j * (j - 1) / 2 }

pub fn coordinate(m: usize, forest: &Forest, survival: &Rational)
    -> Result<Coordinate, &'static str> {
    if !(1..=64).contains(&m) || forest.is_empty() || forest.len() > m { return Err("FOREST_SIZE"); }
    if survival <= &q(0, 1) || survival >= &q(1, 1) { return Err("FOREST_SURVIVAL"); }
    let mut seen = vec![false; m];
    let mut hooks = BigInt::one();
    let mut previous = 0;
    for tree in forest {
        let (_, least) = scan(tree, m, &mut seen, &mut hooks)?;
        if previous >= least { return Err("FOREST_CANONICAL"); }
        previous = least;
    }
    if seen.iter().any(|present| !present) { return Err("FOREST_LABELS"); }
    let roots = forest.len();
    let mergers = m - roots;
    let factorial: BigInt = (1..=mergers).map(BigInt::from).product();
    let (histories, remainder) = factorial.div_rem(&hooks);
    if !remainder.is_zero() { return Err("FOREST_HISTORY"); }
    // The prefactor in P(m,r;x) cancels with the coordinate's history divisor.
    let mut probability = Rational::zero();
    for j in roots..=m {
        let exponent = rate(j);
        let denominator: BigInt = (roots..=m).filter(|other| *other != j)
            .map(|other| BigInt::from(rate(other)) - BigInt::from(exponent)).product();
        probability += Rational::new(histories.clone(), denominator) * survival.pow(exponent as i32);
    }
    if probability < q(0, 1) || probability > q(1, 1) { return Err("FOREST_PROBABILITY"); }
    Ok(Coordinate { roots, mergers, hook_product: hooks, histories, probability })
}

# zeta-rigidity

A Lean 4 / Mathlib formalization. Starting from an abstract set of primes carrying no numerical
information, requiring that a valuation's Dirichlet series agree with the Riemann zeta function
forces that valuation to be the ordinary primes `2, 3, 5, 7, …`.

Complete, with no `sorry`. Every theorem depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## The construction

There are three layers.

1. **Abstract primes.** A list of symbols `p₀, p₁, p₂, …` with an order and nothing else: no
   size, no arithmetic, no claim that they are numbers. The axioms are a least element, a
   successor and an induction principle, which fix the order type to ω.
2. **Formal products.** Finite products of those symbols, such as `p₀³ · p₂`, forming the free
   commutative monoid. An element *is* its exponent vector, so multiplication is the primitive
   operation and unique factorisation holds by definition rather than as a theorem.
3. **A valuation.** A function `v` assigning each symbol `pᵢ` a real number `v i > 1`, increasing
   in `i`, extended multiplicatively to every formal product. At this point `v` is unconstrained
   apart from being increasing: the values need not be integers and are not tied to the primes.

## The main theorem

`ZetaRigidity/Rigidity.lean`:

```lean
theorem eq_nth_prime_of_isZetaNormalized (h : IsZetaNormalized v) (i : ℕ) :
    v i = (Nat.nth Nat.Prime i : ℝ)
```

The hypothesis `IsZetaNormalized v` says the series `∑ₘ v(m)^(-s)` over all formal products
converges and equals `ζ(s)` for every integer `s = 2, 3, 4, …`. The conclusion is that `v i` is
the `i`-th ordinary prime, so `v 0 = 2`, `v 1 = 3`, `v 2 = 5`, and the formal products are
carried bijectively and multiplicatively onto the positive integers. No form of addition is
assumed; the numerical scale comes entirely from the analytic identity.

Agreement is required only at integer arguments, so `ζ(2), ζ(3), ζ(4), …` already determine the
primes. `eq_nth_prime_of_riemannZeta` in `ZetaRigidity/Zeta.lean` is the same statement phrased
against Mathlib's `riemannZeta`.

The proof runs as follows. A Dirichlet series determines its exponents: as `s` grows the
smallest value dominates the sum, so letting `s → ∞` recovers that value and its multiplicity;
peeling off dominant terms shows the two multisets of values agree, and a set of naturals has
only one increasing enumeration. Since the ζ side is built from `1, 2, 3, …`, the valuation side
must be too, and the irreducible elements on each side then correspond.

## Why the hypothesis cannot be weakened

Every integer `≥ 2` is needed. `exists_not_isZetaNormalized_agreeing_at_two`
(`ZetaRigidity/Sharpness.lean`) exhibits a valuation that reproduces `ζ(2)` exactly and is not
the primes: it sends the first prime to `√(45/13) ≈ 1.861` and the second to `4`, leaving
`5, 7, 11, …` unchanged, so the two Euler factors both multiply to `3/2`.

The word "rigidity" is a contrast with the situation before the hypothesis is imposed.
`autEquivPerm` (`ZetaRigidity/Automorphisms.lean`) proves

```lean
MulAut FormalProd ≃* Equiv.Perm ℕ
```

so every permutation of the abstract primes extends to an automorphism of the monoid, and every
automorphism arises this way. Multiplication alone therefore does not distinguish one prime from
another. The ζ-condition reduces this symmetry group to the trivial one.

Restoring the indexing of the primes fixes part of the ordering but not all of it.
`universallyLE_iff` (`ZetaRigidity/UniversalOrder.lean`) identifies exactly which comparisons
hold in every valuation: `v.extend m ≤ v.extend n` for all `v` precisely when, for every `j`,
`m` has at most as many prime factors of index `≥ j` as `n` does. This order lies strictly
between divisibility and a total order. In particular `not_universallyLE_mul` shows `p₀ · p₁`
and `p₂` are incomparable: the ordinary primes give `6 > 5`, while `stepVal 2 1`, which jumps at
the third prime, gives `e³ < e⁴`. Both witnesses are in `ZetaRigidity/Examples.lean`. A total
order has to come from outside, and the ζ-condition is what supplies it.

Two further limits are recorded. Nothing definable from the multiplicative structure alone can
help: by `iff_atom_of_aut_invariant` and `rel_atom_iff_of_aut_invariant`
(`ZetaRigidity/Automorphisms.lean`), any automorphism-invariant property or relation — a graph
on formal products, for instance — is unchanged by relabelling the primes. And strengthening
the order axioms is not enough either: `exists_locallyFinite_order_ne_primes` gives a locally
finite system, with monotone multiplication and increasing atoms, whose order still differs from
the primes'. Its atoms are `3, 5, 7, 11, …`, putting `p₀² = 9` above `p₂ = 7` where the ordinary
primes put `4` below `5`. What `ℤ_{>0}` has and these lack is that its values have no gaps,
which is `isZetaNormalized_of_equiv` and so equivalent to the ζ-condition again.

## Limitations

**The hypothesis is equivalent to the conclusion.** `∑ₘ V(m)^(-s) = ζ(s)` holds if and only if
`V` is a multiplicative bijection onto `ℤ_{>0}`; the converse is `isZetaNormalized_of_equiv` in
`ZetaRigidity/Model.lean`. What the theorem establishes is that a Dirichlet series determines
its exponents. What ζ contributes is the multiset `{1, 2, 3, …}`.

**This is not a route to arithmetic without addition.** Once the magnitude order is available
alongside multiplication, addition is definable. `add_definable`
(`ZetaRigidity/Extensions/Addition.lean`) gives the formula: writing `S` for the order-defined
successor,

```
val R = val P + val Q   ↔   S (P·R) · S (Q·R) = S (S (P·Q) · R · R)
```

and the right-hand side uses only `*` and `S`. `twin_iff`
(`ZetaRigidity/Extensions/Order.lean`) makes the same point concretely: the definition of twin
primes that avoids writing `+ 2` is provably equivalent to `val Q = val P + 2`.

## Layout

The main line, in dependency order:

| File | Contents |
| --- | --- |
| `ZetaRigidity/Primes.lean` | Prime axioms; `equivNat`. Formal products as the free commutative monoid; atoms, degree, irreducibility; the universal property `lift`/`hom_ext`. |
| `ZetaRigidity/Valuation.lean` | `Valuation` and its multiplicative extension. |
| `ZetaRigidity/DirichletUniqueness.lean` | Uniqueness for power sums: local finiteness, fibrewise assembly, the dominant-term limit `tendsto_tsum_pow`. |
| `ZetaRigidity/Rigidity.lean` | `IsZetaNormalized` and the main theorem. |
| `ZetaRigidity/Model.lean` | The intended model; the hypothesis is satisfiable. |
| `ZetaRigidity/Zeta.lean` | The statement against Mathlib's `riemannZeta`. |
| `ZetaRigidity/Sharpness.lean` | One zeta value does not suffice. |
| `ZetaRigidity/Automorphisms.lean` | `autEquivPerm`. |
| `ZetaRigidity/UniversalOrder.lean` | The order the construction fixes on its own: `universallyLE_iff`. |
| `ZetaRigidity/Examples.lean` | Worked examples and regression tests. |

`ZetaRigidity/Extensions/` holds separate developments that build on the same construction but
are not used by the main theorem: the recovered order and twin primes (`Order.lean`),
definability of addition (`Addition.lean`), the Euler product `ζ_P(s) = ∏ₚ (1 - p^(-s))⁻¹` for a
general valuation (`EulerProduct.lean`), the character group as an infinite torus
(`Characters.lean`), and linear independence of `{log p}` over `ℚ` (`LogIndependence.lean`).

### On the analytic core

Uniqueness for generalized Dirichlet series is not in Mathlib.
`Mathlib/NumberTheory/LSeries/Injectivity.lean` runs the same argument, but only for series
indexed by `ℕ` whose exponents are the index; here the exponents are unknown, which is what the
theorem determines. It is therefore imitated rather than applied.

Because ζ is needed only at integer arguments, the core is stated with natural powers rather
than `Real.rpow`. Tannery's theorem then applies directly and `tendsto_tsum_pow` is about 30
lines.

### Relation to generalized prime systems

A `Valuation` together with `FormalProd` is a generalized prime system in the sense of Beurling,
with `extend` as the norm map and `∑ₘ v.extend m ^ (-s)` as the associated zeta function. Two
conventions differ. Divergence of the prime values is not assumed here but derived from
convergence of the series (`Valuation.tendsto_atTop_of_summable`). Repeated prime values are
excluded by `StrictMono`, so this development covers systems with distinct primes; some ordering
assumption is unavoidable, since by `autEquivPerm` a bare monoid admits every permutation of its
primes as a symmetry.

Definitions follow Beurling, *Analyse de la loi asymptotique de la distribution des nombres
premiers généralisés*, Acta Math. **68** (1937), 255–291; H. G. Diamond, *J. Number Theory* **1**
(1969); and Knopfmacher's arithmetical semigroups.

## Building

```sh
lake build
```

Pinned to Lean `v4.34.1` and Mathlib `v4.34.1`. Several lemma names used here are
version-sensitive (`Set.mem_ofPred_eq`, `Nat.infinite_setOfPred_prime`, `Nat.dvd_sub`,
`Finset.one_le_prod₀`), so expect minor breakage when bumping Mathlib.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). This matches Mathlib, which this project depends
on and whose file-header convention it follows.

# zeta-rigidity

A Lean 4 / Mathlib formalization: **the Riemann zeta function rigidifies the multiplicative
monoid**. Starting from an abstract set of primes with no numerical content, requiring that a
valuation's Dirichlet series agree with ζ forces that valuation to be the ordinary primes
`2, 3, 5, 7, …`.

## What this does, concretely

The setup has three layers. First, a bare list of symbols `p₀, p₁, p₂, …` called "abstract
primes": they have an order and nothing else — no size, no arithmetic, not even a claim that they
are numbers. Second, finite formal products of those symbols, such as `p₀³ · p₂`, which form the
free commutative monoid on the symbols. Because an element of that monoid *is* its exponent
vector, multiplication is the primitive operation and unique factorisation holds by definition
rather than as a theorem. Third, a `Valuation`: a function `v` that hands each symbol `pᵢ` a real
number `v i > 1`, increasing in `i`, and extends multiplicatively to every formal product
(`v(p₀³ · p₂) = v(0)³ · v(2)`). At this point `v` is completely unconstrained apart from being
increasing; the values need not be integers, and nothing ties them to the usual primes.

The single constraint added is analytic. Sum `v(m)^(-s)` over all formal products `m`, and require
that this sum equal `ζ(s)` for every integer `s = 2, 3, 4, …`. The theorem is that this one
requirement pins the valuation down completely: `v i` must be the `i`-th ordinary prime, so
`v 0 = 2`, `v 1 = 3`, `v 2 = 5`, and the formal products are carried bijectively and
multiplicatively onto the positive integers. The proof route is that a Dirichlet series determines
its own exponents: as `s` grows the smallest value dominates the sum, so letting `s → ∞` reads that
value and its multiplicity back off the series; peeling off dominant terms shows the two multisets
of values agree, and a set of naturals has only one increasing enumeration. Since the ζ side is
built from `1, 2, 3, …`, the valuation side has to be too, and the multiplicatively indecomposable
elements on each side must then match — abstract primes to ordinary primes. Everything is checked
mechanically in Lean 4 against Mathlib, so the guarantee is that the argument has no gaps, not
merely that it reads convincingly.

Complete, with no `sorry`. Every headline theorem depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## The main theorem

`ZetaRigidity/Rigidity.lean`:

```lean
theorem eq_nth_prime_of_isZetaNormalized (h : IsZetaNormalized v) (i : ℕ) :
    v i = (Nat.nth Nat.Prime i : ℝ)
```

The construction assumes no ordinary addition. Abstract primes are indexed by a structure with a
least element, a successor and an induction principle; finite formal products form the free
commutative monoid, so multiplication is primitive and unique factorisation is definitional. The
only input carrying numerical scale is the analytic identity.

Agreement with ζ is required **only at the integers** `s = 2, 3, 4, …`, so the theorem says: the
values `ζ(2), ζ(3), ζ(4), …` already determine the primes.

## Two things the result does *not* say

Both are recorded in the module docstrings, because both are easy to over-read.

**The hypothesis is equivalent to the conclusion.** `∑_m V(m)^{-s} = ζ(s)` holds *iff* `V` is a
multiplicative bijection onto `ℤ_{>0}` — `isZetaNormalized_of_equiv` in `ZetaRigidity/Model.lean`
is the converse. The content is that a Dirichlet series determines its exponents, not that ζ
mysteriously detects primes. What ζ supplies is the multiset `{1, 2, 3, …}`.

**This is not a route to addition-free number theory.** Once the magnitude order is available
alongside multiplication, addition is first-order definable: successor from the order, divisibility
from multiplication, then `+` by Julia Robinson's theorem (1949). So `(ℤ_{>0}, ×, <)` is
interdefinable with full first-order arithmetic. `twin_iff` in `ZetaRigidity/Order.lean` makes this
concrete: the addition-free structural definition of twin primes is *proved equal* to
`val Q = val P + 2`. Addition was relocated into the order, not eliminated.

The genuine content is the contrast. `(ℤ_{>0}, ×)` alone is Skolem arithmetic — decidable, with
automorphism group the full permutation group of the primes, so "twin primes" is not even
expressible in it. The ζ condition is exactly the bridge from that tame structure to the wild one.

> Robinson's theorem and the decidability of Skolem arithmetic are quoted from memory and should be
> checked against the literature before being relied on.

## Layout

| File | Contents |
| --- | --- |
| `ZetaRigidity/Primes.lean` | Abstract prime axioms; `equivNat` shows any such structure is `ℕ`. Formal products as the free commutative monoid; atoms, degree, irreducibility. |
| `ZetaRigidity/Valuation.lean` | `Valuation` (values `> 1`, strictly monotone) and its multiplicative extension. |
| `ZetaRigidity/DirichletUniqueness.lean` | The analytic engine: local finiteness, fibrewise assembly, the dominant-term limit `tendsto_tsum_pow`, uniqueness for power sums. |
| `ZetaRigidity/Rigidity.lean` | `IsZetaNormalized` and the main theorem. |
| `ZetaRigidity/Model.lean` | The intended model, and **non-vacuity**: the hypothesis is provably satisfiable. |
| `ZetaRigidity/Order.lean` | Reconstructed magnitude order, prime elements, `Twin`, and `twin_iff`. |
| `ZetaRigidity/Examples.lean` | Worked examples and regression tests. |

### On the analytic core

Uniqueness for generalized Dirichlet series is not in Mathlib.
`Mathlib/NumberTheory/LSeries/Injectivity.lean` runs the same argument, but only for series indexed
by `ℕ` whose exponents *are* the index; here the exponents are unknown, which is the theorem. It is
therefore imitated rather than applied.

Because ζ is needed only at integer arguments, the core is stated with **natural** powers rather
than `Real.rpow`. That substitution is what makes it tractable: Tannery's theorem then applies
directly, and `tendsto_tsum_pow` comes out at about 30 lines.

## Testing

`val` and `Valuation.extend` are noncomputable (`Finsupp.single`, `Finsupp.mapDomain` and `Nat.nth`
all are), so `#eval` is unavailable and examples are checked as proofs. The `@[simp]` rules
`val_one`, `val_mul`, `val_atom`, `val_pow` let `simp`/`norm_num` evaluate `val` on any concrete
formal product.

Two tests in `ZetaRigidity/Examples.lean` carry real evidential weight:

* `val_example` / `extend_example` compute `p₀³ · p₂ = 40` by two independently built routes — in
  `ℕ` via `Nat.factorization`, and in `ℝ` via `Finsupp.prod`. They meet only at `coe_val`, so
  agreement exercises that bridge rather than restating a definition.
* `badVal_not_isZetaNormalized` shows the hypothesis excludes something: the valuation `i ↦ i + 3`
  meets every structural requirement and is provably not ζ-normalized.

## Building

```sh
lake build
```

Pinned to Lean `v4.34.1` and Mathlib `v4.34.1`. Several lemma names used here are
version-sensitive (`Set.mem_ofPred_eq`, `Nat.infinite_setOfPred_prime`, `Nat.dvd_sub`,
`Finset.one_le_prod₀`), so expect minor breakage when bumping Mathlib.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). This matches Mathlib, which this project depends on
and whose file-header convention it follows.

## GitHub configuration

For a new GitHub repository:

* Under the repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General", and check
  **Allow GitHub Actions to create and approve pull requests**.
* In the **Pages** section, set the **Source** dropdown to "GitHub Actions".

This section can be removed once done.

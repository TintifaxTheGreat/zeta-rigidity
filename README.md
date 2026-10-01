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
values `ζ(2), ζ(3), ζ(4), …` already determine the primes. `eq_nth_prime_of_riemannZeta` in
`ZetaRigidity/Zeta.lean` is the same statement phrased against Mathlib's `riemannZeta`.

And *every* such integer is needed. `exists_not_isZetaNormalized_agreeing_at_two` in
`ZetaRigidity/Sharpness.lean` exhibits a valuation that reproduces `ζ(2)` exactly and is still not
the primes: it sends the first prime to `√(45/13) ≈ 1.861` and the second to `4`, leaving
`5, 7, 11, …` fixed, so the two Euler factors both multiply to `3/2`.

## This is a Beurling generalized prime system

The construction is not sui generis. It is, object for object, the standard setting of **Beurling
generalized primes** — in Knopfmacher's algebraic form, an *arithmetical semigroup*.

| Here | Beurling theory |
| --- | --- |
| index `ℕ` of `Valuation` | Beurling's subscript `k` in `p_k` |
| `Valuation.toFun : ℕ → ℝ` with `1 < toFun i` | the generalized primes `p_k`, real and `> 1` |
| `FormalProd = Multiplicative (ℕ →₀ ℕ)` | the generalized integers, as a **multiset** |
| `Valuation.extend : FormalProd →* ℝ` | the norm map `\|·\| : 𝒢 → [1, ∞)` |
| `∑' m, v.extend m ^ (-s)` | the Beurling zeta function `ζ_P(s)` |
| `eq_nth_prime_of_isZetaNormalized` | a rigidity theorem for Beurling systems |

So the main theorem reads: **the only Beurling prime system with distinct primes whose zeta
function agrees with ζ at the integers is the system of rational primes.**

The multiset point is the one that is easy to get wrong. Since the primes are unknown reals, two
different exponent vectors may have the same numerical value, so the generalized integers are
indexed by exponent vectors, not by values — which is exactly what the free commutative monoid
gives, and what "unique factorisation is definitional" means above.

Two axioms differ from the standard definition, and the difference runs in both directions:

* **Divergence is derived here, not assumed.** Beurling requires `p_k → ∞`. `Valuation` does not,
  and `i ↦ 2 - 1/(i+2)` is a legal `Valuation` with all values in `[3/2, 2)`. But
  `Valuation.tendsto_atTop_of_summable` shows that convergence of the zeta function anywhere
  forces divergence, so every system the rigidity theorem discusses is a genuine Beurling system.
* **Repeated primes are excluded.** Beurling allows `p_i = p_j`; `StrictMono` does not. This
  development therefore covers Beurling systems with *distinct* primes. That restriction is
  deliberate — `strictMono_eq_of_range_eq` is the endgame of the main proof — and some order
  axiom is indispensable, since by `autEquivPerm` (below) a bare monoid admits every permutation
  of its primes as a symmetry.

Definitions follow Beurling, *Analyse de la loi asymptotique de la distribution des nombres
premiers généralisés*, Acta Math. **68** (1937), 255–291; H. G. Diamond, *J. Number Theory* **1**
(1969); and Knopfmacher's *arithmetical semigroups*.

### The Euler product

`ZetaRigidity/EulerProduct.lean` proves the defining identity of the subject for an arbitrary such
system:

```
ζ_P(s) = ∏_p (1 - p^{-s})⁻¹
```

stated as the limit of the partial products over the first `n` primes, following Mathlib's
convention. Mathlib's `EulerProduct.eulerProduct_completely_multiplicative` cannot be reused:
it is hard-wired to `f : ℕ →*₀ F` over `Nat.primesBelow`, whereas here the primes are unknown.
Nothing on Beurling systems is currently in Mathlib.

The proof iterates the one-prime split `tsum_peel` to get an *exact* finite identity
(`tsum_peel_iter`), which reduces everything to showing the remainder tends to `1`. That last step
is the only analytic content and it genuinely needs the summability hypothesis: the recursion
`A n = (1 - v n^{-s})⁻¹ · A (n+1)` is scale-invariant, so it fixes the ratios but permits any
positive limit. `primeVal_eulerProduct` instantiates the result at the rational primes and
recovers the classical Euler product for `ζ(2)` by a route that never mentions them.

## The dual group, and the vector space that is actually there

Two structural facts about the bare monoid, independent of ζ.

**The dual group is the infinite torus.** A character — a monoid map into the circle — may take
any value whatsoever on each prime, independently, and is then determined. So

```lean
charEquivTorus : (FormalProd →* Circle) ≃* (ℕ → Circle)
```

(`ZetaRigidity/Characters.lean`). This is the same freeness fact as `autEquivPerm`, with
`Equiv.Perm ℕ` replaced by `𝕋^∞`, and both are instances of one universal property
(`lift`/`hom_ext` in `ZetaRigidity/Primes.lean` — Mathlib has no `FreeCommMonoid`). It is the
index-level form of the **Bohr correspondence**: a character sends a formal product to the
monomial `∏ zᵢ^kᵢ`, so a Dirichlet series becomes a power series on the infinite polytorus, and
the vertical shift `s ↦ s + it` becomes the torus point `(v i ^ (-it))ᵢ` (`bohrChar`).

**`FormalProd` is not a vector space** — it is a free commutative *monoid*, with no inverses and
scalars in `ℕ`. The genuinely linear object appears after taking logarithms: `log ∘ extend` is
linear in the exponent vector (`Valuation.log_extend`), and for the rational primes those
coordinates are independent:

```lean
linearIndependent_log_primes :
    LinearIndependent ℚ (fun i : ℕ => Real.log (Nat.nth Nat.Prime i))
```

so `{log p}` is a **basis** of a ℚ-vector space inside `ℝ`
(`ZetaRigidity/LogIndependence.lean`, not in Mathlib). The one substantive step is
`val_injective` — unique factorisation — which is why the result belongs here rather than in a
general analysis library. The `ℤ` case is proved first and promoted by
`LinearIndependent.iff_fractionRing`, so no denominators are cleared by hand.

## Rigid, against what?

The point of the word *rigidity* is a contrast, and both sides of it are theorems.

**Without the ζ condition the structure is maximally symmetric.** `autEquivPerm` in
`ZetaRigidity/Automorphisms.lean` proves `Aut(FormalProd) ≅ Equiv.Perm ℕ`: every permutation of the
abstract primes extends to an automorphism of the multiplicative monoid, and every automorphism
arises that way. So multiplication alone cannot distinguish any prime from any other — a statement
about `2` transports to the same statement about the `10^100`-th prime.

**With it, the valuation is unique.** That is the main theorem. The ζ condition is exactly what
collapses the full symmetric group to the trivial one.

## Two things the result does *not* say

Both are recorded in the module docstrings, because both are easy to over-read.

**The hypothesis is equivalent to the conclusion.** `∑_m V(m)^{-s} = ζ(s)` holds *iff* `V` is a
multiplicative bijection onto `ℤ_{>0}` — `isZetaNormalized_of_equiv` in `ZetaRigidity/Model.lean`
is the converse. The content is that a Dirichlet series determines its exponents, not that ζ
mysteriously detects primes. What ζ supplies is the multiset `{1, 2, 3, …}`.

**This is not a route to addition-free number theory.** Once the magnitude order is available
alongside multiplication, addition comes back — and this is now proved, not cited.
`add_definable` in `ZetaRigidity/Addition.lean` gives the formula explicitly: writing `S` for the
order-defined successor (`msucc_eq_iff`: the least element strictly above, nothing in between),

```
val R = val P + val Q   ↔   S (P·R) · S (Q·R) = S (S (P·Q) · R · R)
```

and the right-hand side mentions only `*` and `S`. So `(ℤ_{>0}, ×, <)` is interdefinable with full
first-order arithmetic. `twin_iff` in `ZetaRigidity/Order.lean` is the same point made concretely:
the addition-free structural definition of twin primes is *proved equal* to `val Q = val P + 2`.
Addition was relocated into the order, not eliminated.

The genuine content is the contrast. `(ℤ_{>0}, ×)` alone is Skolem arithmetic — decidable, and by
`autEquivPerm` above with automorphism group the full permutation group of the primes, so "twin
primes" is not even expressible in it. The ζ condition is the bridge from that tame structure to
the wild one.

The identity used is Robinson's, from J. Robinson, *Definability and decision problems in
arithmetic*, Journal of Symbolic Logic **14** (1949), 98–114, Theorem 1.1: over the positive
integers, addition is first-order definable from multiplication together with successor, and also
from multiplication together with `<`. The polynomial form
`(1+xz)(1+yz) = 1+(1+xy)z² ⟺ x+y=z` (for `z > 0`) is Tarski's identity as presented in Boolos,
Burgess and Jeffrey, *Computability and Logic*, Ch. 24.

> Two caveats remain. `ZetaRigidity/Addition.lean` proves the *semantic* statement — an explicit
> formula over `ℕ`, checked correct — not the model-theoretic `Definable₂` over a formalised
> first-order language for `(×, <)`; Mathlib's `ModelTheory/Arithmetic/` covers only Presburger.
> And the decidability of Skolem arithmetic is still quoted, not proved or checked here.

## Layout

| File | Contents |
| --- | --- |
| `ZetaRigidity/Primes.lean` | Abstract prime axioms; `equivNat` shows any such structure is `ℕ`. Formal products as the free commutative monoid; atoms, degree, `irreducible_iff_isPrimeElt`; the universal property `lift`/`hom_ext`. |
| `ZetaRigidity/Automorphisms.lean` | The tame side: `autEquivPerm : MulAut FormalProd ≃* Equiv.Perm ℕ`. Depends on `Primes.lean` only — no analysis. |
| `ZetaRigidity/Characters.lean` | The dual group: `charEquivTorus : (FormalProd →* Circle) ≃* (ℕ → Circle)`, and the Bohr lift `bohrChar`. |
| `ZetaRigidity/LogIndependence.lean` | `{log p}` is ℚ-linearly independent — the primes as a basis. |
| `ZetaRigidity/Valuation.lean` | `Valuation` (values `> 1`, strictly monotone) — the Beurling prime system — and its multiplicative extension; divergence derived from summability. |
| `ZetaRigidity/DirichletUniqueness.lean` | The analytic engine: local finiteness, fibrewise assembly, the dominant-term limit `tendsto_tsum_pow`, uniqueness for power sums. |
| `ZetaRigidity/Rigidity.lean` | `IsZetaNormalized` and the main theorem. |
| `ZetaRigidity/Model.lean` | The intended model, and **non-vacuity**: the hypothesis is provably satisfiable. |
| `ZetaRigidity/Zeta.lean` | The bridge to Mathlib's `riemannZeta`; the main theorem restated with ζ in it. |
| `ZetaRigidity/Sharpness.lean` | The one-prime Euler split `peelEquiv`, and the counterexample showing one point does not suffice. |
| `ZetaRigidity/EulerProduct.lean` | `ζ_P(s) = ∏_p (1 - p^{-s})⁻¹` for an arbitrary Beurling system; the classical Euler product at `s = 2` as an instance. |
| `ZetaRigidity/Order.lean` | Reconstructed magnitude order, prime elements, `Twin`, and `twin_iff`. |
| `ZetaRigidity/Addition.lean` | `msucc` from the order, and `add_definable`: Robinson's identity, proved. |
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

Two more added with the later files, on the same principle — a test is worth having only if it
could fail:

* the `add_definable` checks accept `2 + 3 = 5` and *reject* `2 + 3 = 6` through the identity
  itself, so the formula is shown to discriminate rather than merely to hold somewhere;
* the `Automorphisms` checks exhibit a non-identity automorphism (`ofPerm (Equiv.swap 0 1)` moves
  `atom 0` to `atom 1`), which is what rules out the correspondence being degenerate.

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

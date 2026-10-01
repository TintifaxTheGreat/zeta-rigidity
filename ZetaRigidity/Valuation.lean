/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Primes

/-!
# The unknown valuation

A `Valuation` assigns to each abstract prime a real number `> 1`, strictly increasingly. It
extends uniquely and multiplicatively to all of `FormalProd` (`Valuation.extend`), which is the
map the ζ-condition will later pin down.

Nothing here assumes the values are integers, or indeed related to the ordinary primes at all:
that is precisely what the rigidity theorem has to prove.

## This is a Beurling generalized prime system

`Valuation` is not a new notion. A *Beurling generalized prime system* is a sequence of reals
`1 < p₁ ≤ p₂ ≤ …` tending to infinity, and `Valuation.extend` on `FormalProd` is the associated
system of *generalized integers* -- Knopfmacher's *arithmetical semigroup*, the free commutative
monoid on the primes equipped with a norm map into `[1, ∞)`. The Dirichlet series
`∑' m, v.extend m ^ (-s)` is the Beurling zeta function `ζ_P(s)`.

The index type here is `ℕ`, which is Beurling's subscript `k`; the *values* `v i` are genuine
reals and are unconstrained until the ζ-condition is imposed.

Two axioms differ from the standard definition (Beurling 1937; H. G. Diamond, *J. Number
Theory* 1969; Schlage-Puchta--Vindas), and both are worth stating plainly.

* **Divergence is derived, not assumed.** Beurling requires `p_k → ∞`; the axioms below do not
  give it, and `i ↦ 2 - 1/(i+2)` is a legal `Valuation` with all values in `[3/2, 2)`. But
  `tendsto_atTop_of_summable` at the end of this file shows that as soon as the zeta function
  converges anywhere, divergence follows. So every system the rigidity theorem talks about is a
  genuine Beurling system.
* **Repeated primes are excluded.** Beurling allows `p_i = p_j`; `StrictMono` does not. So this
  development covers Beurling systems with *distinct* primes. The restriction is deliberate:
  `strictMono_eq_of_range_eq` (`ZetaRigidity/Rigidity.lean`) is the endgame of the main proof.
  And some order axiom is indispensable -- by `autEquivPerm`
  (`ZetaRigidity/Automorphisms.lean`), without one every permutation of the primes is a symmetry
  of the monoid, so no indexing could be pinned down at all.
-/

namespace ZetaRigidity

open scoped BigOperators

/-- An assignment of a real magnitude `> 1` to each abstract prime, strictly increasing in the
canonical ordering of the primes. -/
structure Valuation where
  /-- The value of the `i`-th abstract prime. -/
  toFun : ℕ → ℝ
  /-- Every prime has magnitude greater than `1`. -/
  one_lt' : ∀ i, 1 < toFun i
  /-- The canonical ordering of the primes is respected. -/
  strictMono' : StrictMono toFun

namespace Valuation

instance : CoeFun Valuation (fun _ => ℕ → ℝ) := ⟨toFun⟩

variable (v : Valuation)

lemma one_lt (i : ℕ) : 1 < v i := v.one_lt' i

lemma pos (i : ℕ) : 0 < v i := lt_trans one_pos (v.one_lt i)

lemma strictMono : StrictMono v := v.strictMono'

/-- The multiplicative extension of `v` to all formal products: a formal product is sent to the
product of its primes' values, with multiplicity. -/
noncomputable def extend : FormalProd →* ℝ where
  toFun m := (Multiplicative.toAdd m).prod fun i k => v i ^ k
  map_one' := by simp
  map_mul' _ _ := Finsupp.prod_add_index' (by simp) (by simp [pow_add])

@[simp] lemma extend_one : v.extend 1 = 1 := map_one _

@[simp] lemma extend_mul (m n : FormalProd) : v.extend (m * n) = v.extend m * v.extend n :=
  map_mul _ _ _

@[simp] lemma extend_atom (i : ℕ) : v.extend (atom i) = v i := by
  change (Finsupp.single i 1).prod (fun j k => v j ^ k) = v i
  rw [Finsupp.prod_single_index] <;> simp

/-- Every formal product has magnitude at least `1`. -/
lemma one_le_extend (m : FormalProd) : 1 ≤ v.extend m :=
  Finset.one_le_prod₀ fun i _ => one_le_pow₀ (v.one_lt i).le

lemma extend_pos (m : FormalProd) : 0 < v.extend m :=
  lt_of_lt_of_le one_pos (v.one_le_extend m)

/-- Only the empty product has magnitude `1`; every nontrivial formal product is strictly
bigger. This is what makes `1` the least element of the reconstructed order. -/
lemma one_lt_extend {m : FormalProd} (hm : m ≠ 1) : 1 < v.extend m := by
  obtain ⟨i, hi⟩ : (Multiplicative.toAdd m).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun h => hm (Multiplicative.toAdd.injective h)
  change 1 < (Multiplicative.toAdd m).prod fun j k => v j ^ k
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hi]
  have h1 : 1 < v i ^ (Multiplicative.toAdd m) i :=
    one_lt_pow₀ (v.one_lt i) (Finsupp.mem_support_iff.mp hi)
  have h2 : (1 : ℝ) ≤ ∏ j ∈ (Multiplicative.toAdd m).support.erase i,
      v j ^ (Multiplicative.toAdd m) j :=
    Finset.one_le_prod₀ fun j _ => one_le_pow₀ (v.one_lt j).le
  nlinarith

lemma extend_eq_one_iff {m : FormalProd} : v.extend m = 1 ↔ m = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hm
  exact absurd h (v.one_lt_extend hm).ne'

/-! ## Divergence

A `Valuation` is not quite a Beurling prime system: Beurling additionally requires `p_k → ∞`,
and the axioms above do not give it (`i ↦ 2 - 1/(i+2)` has values in `[3/2, 2)` and is a perfectly
legal `Valuation`). The two lemmas below close the gap where it matters: as soon as the Dirichlet
series converges anywhere, divergence follows. So the Beurling axiom is *derived* here rather than
assumed, and every `Valuation` the rigidity theorem talks about really is a Beurling system.
-/

/-- The series over all formal products restricts to the primes, since the atoms embed. -/
lemma summable_atoms {s : ℝ} (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Summable fun i : ℕ => v i ^ (-s) :=
  (h.comp_injective atom_injective).congr fun i => by rw [Function.comp_apply, v.extend_atom]

/-- **The primes tend to infinity.** This is Beurling's divergence axiom, obtained from
convergence of the zeta function rather than imposed. -/
theorem tendsto_atTop_of_summable {s : ℝ} (hs : 0 < s)
    (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Filter.Tendsto v Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop_of_monotone' v.strictMono.monotone ?_
  -- Were the values bounded by `B`, every term would be at least `B ^ (-s) > 0`.
  rintro ⟨B, hB⟩
  have hB' : ∀ i, v i ≤ B := fun i => hB ⟨i, rfl⟩
  have hpos : (0 : ℝ) < B := lt_of_lt_of_le (v.pos 0) (hB' 0)
  have hlow : ∀ i, B ^ (-s) ≤ v i ^ (-s) := by
    intro i
    rw [Real.rpow_neg hpos.le, Real.rpow_neg (v.pos i).le]
    exact inv_anti₀ (Real.rpow_pos_of_pos (v.pos i) s)
      (Real.rpow_le_rpow (v.pos i).le (hB' i) hs.le)
  have hzero := (v.summable_atoms h).tendsto_atTop_zero
  have := ge_of_tendsto' hzero (fun i => hlow i)
  exact absurd this (not_le.mpr (Real.rpow_pos_of_pos hpos _))

/-! ## Passing to logarithms

`extend` is multiplicative; its logarithm is therefore *linear* in the exponent vector. This is
the bridge from the free commutative monoid to a genuinely linear object: the exponent vectors
sit inside a `ℚ`-vector space with the `Real.log (v i)` as coordinates. See
`ZetaRigidity/LogIndependence.lean` for the statement that, for the rational primes, those
coordinates really are a basis.
-/

/-- The logarithm of a formal product's magnitude is the exponent-weighted sum of the
logarithms of its primes. -/
lemma log_extend (v : Valuation) (m : FormalProd) :
    Real.log (v.extend m) = (Multiplicative.toAdd m).sum fun i k => k * Real.log (v i) := by
  change Real.log ((Multiplicative.toAdd m).prod fun i k => v i ^ k) = _
  rw [Finsupp.prod, Real.log_prod fun i _ => (pow_pos (v.pos i) _).ne']
  exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _

end Valuation

end ZetaRigidity

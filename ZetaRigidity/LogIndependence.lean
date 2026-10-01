/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Model

/-!
# The primes are a basis: `{log p}` is linearly independent over `ℚ`

`FormalProd` is a free commutative **monoid**, not a vector space -- it has no inverses and its
scalars are `ℕ`. The genuinely linear object attached to the construction appears after taking
logarithms. `Valuation.log_extend` (`ZetaRigidity/Valuation.lean`) says `log ∘ extend` is linear
in the exponent vector, and this file supplies the missing half: for the rational primes those
coordinates are *independent*, so the primes form a basis of a `ℚ`-vector space inside `ℝ`.

## Main result

`linearIndependent_log_primes : LinearIndependent ℚ (fun i : ℕ => Real.log (Nat.nth Nat.Prime i))`

Not in Mathlib. It belongs here because the one substantive step is `val_injective`
(`ZetaRigidity/Model.lean`) -- that is, unique factorisation, which this development has
definitionally.

## Method

Prove the `ℤ` statement and promote it: `LinearIndependent.iff_fractionRing ℤ ℚ` applies to `ℝ`
directly, so no denominators have to be cleared by hand.

For the `ℤ` statement, a relation `∑ lᵢ · log pᵢ = 0` is split into its positive and negative
parts, giving two honest formal products `m⁺` and `m⁻` with `log (val m⁺) = log (val m⁻)`. Since
`log` is injective on positives this forces `val m⁺ = val m⁻`, and `val_injective` then gives
`m⁺ = m⁻`. Comparing exponents, `(lᵢ).toNat = (-lᵢ).toNat`, which forces `lᵢ = 0`.
-/

namespace ZetaRigidity

open Finsupp

/-- The positive part of an integer exponent vector, as a formal product. -/
private noncomputable def posPart (l : ℕ →₀ ℤ) : FormalProd :=
  Multiplicative.ofAdd (l.mapRange Int.toNat Int.toNat_zero)

private lemma expo_posPart (l : ℕ →₀ ℤ) (i : ℕ) : expo (posPart l) i = (l i).toNat := rfl

private lemma support_posPart (l : ℕ →₀ ℤ) :
    (Multiplicative.toAdd (posPart l)).support ⊆ l.support := by
  change (l.mapRange Int.toNat Int.toNat_zero).support ⊆ l.support
  exact Finsupp.support_mapRange

/-- The logarithm of the value of a formal product, summed over any finite set containing its
support. -/
private lemma log_val_eq_sum (m : FormalProd) {s : Finset ℕ}
    (hs : (Multiplicative.toAdd m).support ⊆ s) :
    Real.log (val m) = ∑ i ∈ s, (expo m i : ℝ) * Real.log (Nat.nth Nat.Prime i) := by
  rw [coe_val, primeVal.log_extend]
  exact Finsupp.sum_of_support_subset _ hs _ (fun i _ => by simp)

/-- **Linear independence over `ℤ`.** This is where unique factorisation is used. -/
theorem linearIndependent_int_log_primes :
    LinearIndependent ℤ (fun i : ℕ => Real.log (Nat.nth Nat.Prime i)) := by
  rw [linearIndependent_iff]
  intro l hl
  -- Rewrite the relation as an ordinary sum over `l.support`.
  rw [Finsupp.linearCombination_apply] at hl
  have hlsum : ∑ i ∈ l.support, (l i : ℝ) * Real.log (Nat.nth Nat.Prime i) = 0 := by
    rw [← hl, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => (zsmul_eq_mul _ _).symm
  -- The two sides of the relation, as genuine formal products.
  have hple : Real.log (val (posPart l))
      = ∑ i ∈ l.support, ((l i).toNat : ℝ) * Real.log (Nat.nth Nat.Prime i) :=
    log_val_eq_sum _ (support_posPart l)
  have hnle : Real.log (val (posPart (-l)))
      = ∑ i ∈ l.support, (((-l) i).toNat : ℝ) * Real.log (Nat.nth Nat.Prime i) :=
    log_val_eq_sum _ ((support_posPart (-l)).trans (le_of_eq (Finsupp.support_neg l)))
  -- Their logarithms agree, since `(l i).toNat - (-l i).toNat = l i`.
  have hlog : Real.log (val (posPart l)) = Real.log (val (posPart (-l))) := by
    rw [hple, hnle, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hlsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_mul]
    congr 1
    simp only [Finsupp.neg_apply]
    exact_mod_cast Int.toNat_sub_toNat_neg (l i)
  -- `log` is injective on positives, so the two values agree.
  have hval : val (posPart l) = val (posPart (-l)) := by
    have h1 : (0 : ℝ) < (val (posPart l) : ℝ) := by exact_mod_cast val_pos _
    have h2 : (0 : ℝ) < (val (posPart (-l)) : ℝ) := by exact_mod_cast val_pos _
    have h3 := congrArg Real.exp hlog
    rw [Real.exp_log h1, Real.exp_log h2] at h3
    exact_mod_cast h3
  -- Unique factorisation: equal values mean equal formal products, hence equal exponents.
  have hpn := val_injective hval
  refine Finsupp.ext fun i => ?_
  have hexp : (l i).toNat = ((-l) i).toNat := by
    have h := congrArg (fun m => expo m i) hpn
    simpa [expo_posPart] using h
  simp only [Finsupp.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at hexp ⊢
  omega

/-- **The primes are a basis.** Over `ℚ` -- and hence the `ℚ`-span of `{log p}` inside `ℝ` is a
vector space with the `log p` as a basis, which is the honest linear object attached to this
construction. `FormalProd` itself is only a monoid. -/
theorem linearIndependent_log_primes :
    LinearIndependent ℚ (fun i : ℕ => Real.log (Nat.nth Nat.Prime i)) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).mp linearIndependent_int_log_primes

end ZetaRigidity

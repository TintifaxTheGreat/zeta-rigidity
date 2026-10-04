/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Valuation

/-!
# Divergence of the prime values

A fact about `Valuation` that the rigidity theorem does not use, collected here rather than in
`ZetaRigidity/Valuation.lean` so that the main line stays limited to what it needs.

## Main results

* `Valuation.summable_atoms`: summability restricts from formal products to the primes.
* `Valuation.tendsto_atTop_of_summable`: if the Dirichlet series converges at one point then the
  prime values tend to infinity.

Used by the other modules in `ZetaRigidity/Extensions/`.
-/

namespace ZetaRigidity

namespace Valuation

variable (v : Valuation)

/-! ## Divergence of the prime values

A `Valuation` need not have `v i → ∞`: the values of `i ↦ 2 - 1/(i+2)` lie in `[3/2, 2)` and
satisfy both axioms. Convergence of the Dirichlet series forces divergence, so the condition
does not have to be assumed separately. In the terminology of generalized prime systems this is
Beurling's requirement that `p_k → ∞`.
-/

/-- Summability over all formal products restricts to summability over the primes, because the
atoms embed into `FormalProd`. -/
lemma summable_atoms {s : ℝ} (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Summable fun i : ℕ => v i ^ (-s) :=
  (h.comp_injective atom_injective).congr fun i => by rw [Function.comp_apply, v.extend_atom]

/-- If the Dirichlet series of `v` converges at some `s > 0`, the prime values tend to infinity. -/
theorem tendsto_atTop_of_summable {s : ℝ} (hs : 0 < s)
    (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Filter.Tendsto v Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop_of_monotone' v.strictMono.monotone ?_
  -- If the values were bounded by `B`, every term would be at least `B ^ (-s) > 0`.
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

end Valuation

end ZetaRigidity

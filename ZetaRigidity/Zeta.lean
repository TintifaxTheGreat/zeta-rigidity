/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Rigidity
import ZetaRigidity.Model

/-!
# The hypothesis stated with `riemannZeta`

`IsZetaNormalized` (`ZetaRigidity/Rigidity.lean`) is stated against the explicit sum
`∑' n, ((n : ℝ) + 1) ^ (-k)`. This file proves that sum equals Mathlib's `riemannZeta` at
integer arguments, so the connection is checked rather than assumed.

## Main results

* `ofReal_tsum_natSucc_eq_riemannZeta`: the explicit sum, cast to `ℂ`, equals `riemannZeta k`.
* `IsZetaNormalized.agrees_riemannZeta` and `IsZetaNormalized.of_riemannZeta`: the two phrasings
  of the hypothesis are interchangeable.
* `eq_nth_prime_of_riemannZeta`: the rigidity theorem with `riemannZeta` in its statement.

All arguments are integers, so `Complex.cpow` appears only to quote Mathlib and is discharged by
`Complex.cpow_natCast`.
-/

namespace ZetaRigidity

open Complex

/-! ## The sum in the hypothesis, identified -/

/-- Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow` at an integer argument, with the `cpow`
replaced by an ordinary power. -/
lemma riemannZeta_nat_eq_tsum_inv_pow {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, (((n : ℂ) + 1) ^ k)⁻¹ := by
  have hre : 1 < ((k : ℂ)).re := by
    rw [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt]
    exact hk
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  exact tsum_congr fun n => by rw [cpow_natCast, one_div]

/-- The real sum appearing in `IsZetaNormalized.agrees` equals `riemannZeta k`.

The proof rewrites the negative real power as an inverse natural power
(`rpow_neg_natCast_eq_inv_pow`), pushes the cast through the `tsum` (`Complex.ofReal_tsum`), and
compares with `riemannZeta_nat_eq_tsum_inv_pow`. -/
theorem ofReal_tsum_natSucc_eq_riemannZeta {k : ℕ} (hk : 1 < k) :
    ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k := by
  rw [riemannZeta_nat_eq_tsum_inv_pow hk, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [rpow_neg_natCast_eq_inv_pow hpos, ← inv_pow]
  push_cast
  ring

/-! ## The hypothesis, restated -/

variable {v : Valuation}

/-- The ζ-hypothesis is agreement with `riemannZeta`. -/
theorem IsZetaNormalized.agrees_riemannZeta (h : IsZetaNormalized v) {k : ℕ} (hk : 2 ≤ k) :
    ((∑' m : FormalProd, v.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k := by
  rw [h.agrees k hk]
  exact ofReal_tsum_natSucc_eq_riemannZeta (by omega)

/-- Conversely, agreement with `riemannZeta` at the integers establishes the hypothesis. Together
with `IsZetaNormalized.agrees_riemannZeta` this says the two phrasings are interchangeable. -/
theorem IsZetaNormalized.of_riemannZeta
    (hsum : Summable fun m : FormalProd => v.extend m ^ (-2 : ℝ))
    (hz : ∀ k : ℕ, 2 ≤ k →
      ((∑' m : FormalProd, v.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k) :
    IsZetaNormalized v where
  summable := hsum
  agrees k hk := by
    have h := (hz k hk).trans (ofReal_tsum_natSucc_eq_riemannZeta (k := k) (by omega)).symm
    exact_mod_cast h

/-- ζ-rigidity, with ζ in the statement. If the Dirichlet series of `v` agrees with the
Riemann zeta function at every integer `≥ 2`, then the `i`-th abstract prime has value the `i`-th
ordinary prime. -/
theorem eq_nth_prime_of_riemannZeta
    (hsum : Summable fun m : FormalProd => v.extend m ^ (-2 : ℝ))
    (hz : ∀ k : ℕ, 2 ≤ k →
      ((∑' m : FormalProd, v.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k) (i : ℕ) :
    v i = (Nat.nth Nat.Prime i : ℝ) :=
  eq_nth_prime_of_isZetaNormalized (IsZetaNormalized.of_riemannZeta hsum hz) i

/-! ## Non-vacuity

The check of `primeVal_isZetaNormalized` (`ZetaRigidity/Model.lean`), repeated for the
`riemannZeta` phrasing, so that the theorem above is not vacuous.
-/

/-- The intended valuation's Dirichlet series equals the Riemann zeta function at the
integers. -/
theorem primeVal_agrees_riemannZeta {k : ℕ} (hk : 2 ≤ k) :
    ((∑' m : FormalProd, primeVal.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k :=
  primeVal_isZetaNormalized.agrees_riemannZeta hk

end ZetaRigidity

/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Examples
import ZetaRigidity.Extensions.Order
import ZetaRigidity.Extensions.Addition
import ZetaRigidity.Extensions.EulerProduct
import ZetaRigidity.Extensions.Characters
import ZetaRigidity.Extensions.LogIndependence

/-!
# Tests for the extension modules

Regression tests for the material in `ZetaRigidity/Extensions/`, in the same style as
`ZetaRigidity/Examples.lean`: proofs rather than `#eval`, and preferring checks that could fail
over checks that restate a definition. `example40`, `val_example` and `extend_example` are reused
from the main test file.
-/

namespace ZetaRigidity

/-! ## Prime elements and the reconstructed order -/

example : IsPrimeElt (atom 3) := by
  rw [isPrimeElt_iff, val_atom, Nat.nth_prime_three_eq_seven]
  norm_num

/-- `40` is composite, so `example40` is not a prime element. -/
example : ¬ IsPrimeElt example40 := by
  rw [isPrimeElt_iff, val_example]
  norm_num

example : MLt (atom 0) (atom 1) := by
  simp only [MLt, val_atom, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  norm_num

/-! ## Twin primes: positive and negative cases -/

example : Twin (atom 1) (atom 2) := by
  rw [twin_iff, val_atom, val_atom, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  norm_num

example : Twin (atom 2) (atom 3) := by
  rw [twin_iff, val_atom, val_atom, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
  norm_num

/-- `(2, 3)` are consecutive primes but the gap is `1`, not `2`. -/
example : ¬ Twin (atom 0) (atom 1) := by
  rw [twin_iff, val_atom, val_atom, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  norm_num

/-- `(7, 11)` are consecutive primes but the gap is `4`. -/
example : ¬ Twin (atom 3) (atom 4) := by
  rw [twin_iff, val_atom, val_atom, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  norm_num

/-- `(3, 7)` differ by `4` and are not even consecutive. -/
example : ¬ Twin (atom 1) (atom 3) := by
  rw [twin_iff, val_atom, val_atom, Nat.nth_prime_one_eq_three, Nat.nth_prime_three_eq_seven]
  norm_num

/-! ## Definability of addition

Checks on `ZetaRigidity/Extensions/Addition.lean`. The identity must accept genuine sums and
reject near misses. -/

/-- Accepts a true sum: `2 + 3 = 5`. -/
example : (1 + 2 * 5) * (1 + 3 * 5) = 1 + (1 + 2 * 3) * (5 * 5) := by norm_num

/-- Rejects a near miss: `2 + 3 ≠ 6`, and the identity sees it. -/
example : ¬ ((1 + 2 * 6) * (1 + 3 * 6) = 1 + (1 + 2 * 3) * (6 * 6)) := by norm_num

/-- The successor of the formal product for `40` has value `41`. -/
example : val (msucc example40) = 41 := by rw [val_msucc, val_example]

/-- The order-theoretic characterisation agrees: nothing lies strictly between `40` and its
successor. This is what makes `msucc` definable from `<` alone. -/
example : MLt example40 (msucc example40) ∧ ∀ r, ¬ (MLt example40 r ∧ MLt r (msucc example40)) :=
  (msucc_eq_iff example40 (msucc example40)).mp rfl

/-! ## The Euler product

Checks on `ZetaRigidity/Extensions/EulerProduct.lean`. An off-by-one in the relabelling
`shiftIter` or in its range characterisation would produce a wrong Euler product, so those are
what is tested. -/

/-- Relabelling by `2` sends the first prime to the third. -/
example : shiftIter 2 (atom 0) = atom 2 := by
  refine ext_expo fun i => ?_
  rw [expo_shiftIter]
  rcases i with _ | _ | _ | j <;> simp


/-- `p₀³ · p₂` uses the first prime, so it is not in the image of `shiftIter 1`, which consists
of the products avoiding `p₀`. -/
example : example40 ∉ Set.range (shiftIter 1) := by
  rw [mem_range_shiftIter]
  intro h
  have := h 0 (by norm_num)
  simp [example40] at this

/-- The atoms from the second prime on are in the image. -/
example : atom 3 ∈ Set.range (shiftIter 1) := by
  rw [mem_range_shiftIter]
  intro i hi
  interval_cases i
  simp

/-! ### Divergence

`tendsto_atTop_of_summable` derives `v i → ∞` rather than assuming it. The negative example
shows a `Valuation` need not diverge on its own, so the summability hypothesis is needed. -/

example : Filter.Tendsto primeVal Filter.atTop Filter.atTop :=
  primeVal.tendsto_atTop_of_summable (by norm_num) primeVal_summable

/-- A `Valuation` whose values stay below `2`. Divergence therefore cannot be read off the
`Valuation` axioms and has to be derived from convergence of the series. -/
noncomputable def boundedVal : Valuation where
  toFun i := 2 - 1 / ((i : ℝ) + 2)
  one_lt' i := by
    have h : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have : 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · simp
    linarith
  strictMono' a b hab := by
    have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
    have hlt : ((a : ℝ) + 2) < ((b : ℝ) + 2) := by
      have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      linarith
    have := one_div_lt_one_div_of_lt ha hlt
    dsimp only
    linarith

example (i : ℕ) : boundedVal i < 2 := by
  have h : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have : 0 < 1 / ((i : ℝ) + 2) := by positivity
  simp only [boundedVal]
  linarith

/-- So it does not tend to infinity, and hence its Dirichlet series cannot converge. -/
example : ¬ Filter.Tendsto boundedVal Filter.atTop Filter.atTop := by
  intro h
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp h 2).exists_forall_of_atTop
  have hb : boundedVal N < 2 := by
    have h0 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have : 0 < 1 / ((N : ℝ) + 2) := by positivity
    simp only [boundedVal]
    linarith
  exact absurd (hN N le_rfl) (not_le.mpr hb)

/-! ## The character group -/

/-- The correspondence is a group isomorphism, so it maps the trivial character to the identity
point of the torus. -/
example : charEquivTorus 1 = 1 := charEquivTorus.map_one

/-- It is not constantly trivial: `signChar` has value `-1` in the first coordinate. -/
example : charEquivTorus signChar 0 = Circle.exp Real.pi := signChar_atom_zero

/-! ## Linear independence of logarithms

Checks on `ZetaRigidity/Extensions/LogIndependence.lean`. The first shows no nonzero integer
relation holds among `log 2`, `log 3`, `log 5`. The second shows the theorem is not vacuously
true of all logarithms, since relations exist for non-primes. -/

example (a b c : ℤ)
    (h : (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 + (c : ℝ) * Real.log 5 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hli := linearIndependent_iff.mp linearIndependent_int_log_primes
  set l : ℕ →₀ ℤ := Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c with hldef
  have hzero : l = 0 := by
    refine hli l ?_
    simp only [hldef, map_add, Finsupp.linearCombination_single, zsmul_eq_mul,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
    push_cast
    linarith [h]
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun f : ℕ →₀ ℤ => f 0) hzero; simpa [hldef] using this
  · have := congrArg (fun f : ℕ →₀ ℤ => f 1) hzero; simpa [hldef] using this
  · have := congrArg (fun f : ℕ →₀ ℤ => f 2) hzero; simpa [hldef] using this

/-- Primality is needed: `log 2` and `log 4` are dependent. -/
example : 2 * Real.log 2 - Real.log 4 = 0 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

end ZetaRigidity

/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Order

/-!
# Worked examples and regression tests

`val` and `Valuation.extend` are noncomputable -- `Finsupp.single`, `Finsupp.mapDomain` and
`Nat.nth` all are -- so `#eval` is unavailable and examples have to be checked as *proofs*. The
`@[simp]` computation rules in `ZetaRigidity/Model.lean` (`val_one`, `val_mul`, `val_atom`,
`val_pow`) make that mechanical: `simp`/`norm_num` evaluate `val` on any concrete formal product.

The sharpest test here is `extend_example`/`val_example`: `val` is built in `ℕ` out of
`Nat.factorization` and `Finsupp.mapDomain`, while `Valuation.extend` is built in `ℝ` out of
`Finsupp.prod`. They are separate definitions joined only by `coe_val`, so agreeing on a
concrete product genuinely exercises that bridge rather than restating a definition.

`badVal_not_isZetaNormalized` at the end is the test with the most evidential value: it checks
that the ζ-hypothesis actually excludes something.
-/

namespace ZetaRigidity

/-! ## The valuation on individual primes -/

example : primeVal 0 = 2 := by simp [primeVal, Nat.nth_prime_zero_eq_two]
example : primeVal 1 = 3 := by simp [primeVal, Nat.nth_prime_one_eq_three]
example : primeVal 2 = 5 := by simp [primeVal, Nat.nth_prime_two_eq_five]
example : primeVal 3 = 7 := by simp [primeVal, Nat.nth_prime_three_eq_seven]
example : primeVal 4 = 11 := by simp [primeVal, Nat.nth_prime_four_eq_eleven]

/-! ## A worked example: the formal product `p₀³ · p₂`, which should be `2³ · 5 = 40` -/

/-- The example formal product: three copies of the first prime and one of the third. -/
noncomputable def example40 : FormalProd := atom 0 ^ 3 * atom 2

/-- Computed in `ℕ`, through `Nat.factorization` and `Finsupp.mapDomain`. -/
theorem val_example : val example40 = 40 := by
  simp [example40, Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]

/-- Computed independently in `ℝ`, through `Finsupp.prod` over the real values. Agreement with
`val_example` is the real test: these two definitions meet only at `coe_val`. -/
theorem extend_example : primeVal.extend example40 = 40 := by
  rw [← coe_val, val_example]
  norm_num

/-- Multiplicativity, checked on concrete operands rather than in general: `8 * 5 = 40`. -/
example : val (atom 0 ^ 3) * val (atom 2) = val example40 := by
  simp [example40]

/-- Unique factorisation, concretely: `40` is represented by *only* this formal product. -/
example (m : FormalProd) (hm : val m = 40) : m = example40 :=
  val_injective (by rw [hm, val_example])

/-- `modelEquiv` is `val` shifted down by one, so `40` sits at index `39`. -/
example : modelEquiv example40 = 39 := by
  have h : (modelEquiv example40 : ℕ) = val example40 - 1 := rfl
  rw [h, val_example]

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

/-! ## A negative test: a wrong valuation is rejected

The checks above all confirm the *intended* valuation behaves as expected. This one confirms the
rigidity theorem actually excludes something: a valuation sending the primes to `3, 4, 5, …`
satisfies every structural requirement (values `> 1`, strictly increasing) and is still not
ζ-normalized. -/

/-- A structurally valid but numerically wrong valuation: `i ↦ i + 3`. -/
noncomputable def badVal : Valuation where
  toFun i := (i : ℝ) + 3
  one_lt' i := by have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith
  strictMono' _ _ h := by simpa using h

example : badVal 0 = 3 := by norm_num [badVal]

/-- This is the test that shows the rigidity theorem has teeth: the ζ-hypothesis is not
satisfied by just any increasing valuation. It runs through
`eq_nth_prime_of_isZetaNormalized`. -/
theorem badVal_not_isZetaNormalized : ¬ IsZetaNormalized badVal := by
  intro h
  have h0 := eq_nth_prime_of_isZetaNormalized h 0
  rw [Nat.nth_prime_zero_eq_two] at h0
  norm_num [badVal] at h0

end ZetaRigidity

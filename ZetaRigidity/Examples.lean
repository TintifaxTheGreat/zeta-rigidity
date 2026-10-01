/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Zeta
import ZetaRigidity.Automorphisms
import ZetaRigidity.Sharpness

/-!
# Worked examples and regression tests

`val` and `Valuation.extend` are noncomputable, because `Finsupp.single`, `Finsupp.mapDomain` and
`Nat.nth` are, so `#eval` is unavailable and the examples are stated as proofs. The `@[simp]`
rules in `ZetaRigidity/Model.lean` (`val_one`, `val_mul`, `val_atom`, `val_pow`) let `simp` and
`norm_num` evaluate `val` on any concrete formal product.

Two of these tests carry more weight than the rest. `val_example` and `extend_example` compute
the same number by two separately defined routes that meet only at `coe_val`.
`badVal_not_isZetaNormalized` shows the hypothesis of the main theorem excludes something.

Tests for the modules in `ZetaRigidity/Extensions/` are in `ZetaRigidity/Extensions/Examples.lean`.
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

/-- Computed independently in `ℝ`, through `Finsupp.prod` over the real values. The two
definitions meet only at `coe_val`, so agreement between them is informative. -/
theorem extend_example : primeVal.extend example40 = 40 := by
  rw [← coe_val, val_example]
  norm_num

/-- Multiplicativity, checked on concrete operands rather than in general: `8 * 5 = 40`. -/
example : val (atom 0 ^ 3) * val (atom 2) = val example40 := by
  simp [example40]

/-- Unique factorisation: `40` is represented by this formal product and no other. -/
example (m : FormalProd) (hm : val m = 40) : m = example40 :=
  val_injective (by rw [hm, val_example])

/-- `modelEquiv` is `val` shifted down by one, so `40` sits at index `39`. -/
example : modelEquiv example40 = 39 := by
  have h : (modelEquiv example40 : ℕ) = val example40 - 1 := rfl
  rw [h, val_example]

/-! ## A negative test

The checks above confirm the intended valuation behaves as expected. This one confirms the
rigidity theorem excludes something: a valuation sending the primes to `3, 4, 5, …` satisfies
both `Valuation` axioms and is not ζ-normalized. -/

/-- A valuation satisfying both axioms but with the wrong values: `i ↦ i + 3`. -/
noncomputable def badVal : Valuation where
  toFun i := (i : ℝ) + 3
  one_lt' i := by have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith
  strictMono' _ _ h := by simpa using h

example : badVal 0 = 3 := by norm_num [badVal]

/-- The ζ-hypothesis is not satisfied by every increasing valuation. Proved through
`eq_nth_prime_of_isZetaNormalized`. -/
theorem badVal_not_isZetaNormalized : ¬ IsZetaNormalized badVal := by
  intro h
  have h0 := eq_nth_prime_of_isZetaNormalized h 0
  rw [Nat.nth_prime_zero_eq_two] at h0
  norm_num [badVal] at h0

/-! ## The automorphism group

Checks on `ZetaRigidity/Automorphisms.lean`, confirming the correspondence is not constantly
the identity and respects the group structure on both sides.
-/

/-- A transposition of the primes moves `atom 0` to `atom 1`. Without the ζ-condition nothing
prevents this. -/
example : ofPerm (Equiv.swap 0 1) (atom 0) = atom 1 := by
  rw [ofPerm_atom, Equiv.swap_apply_left]

example : ofPerm (Equiv.swap 0 1) (atom 1) = atom 0 := by
  rw [ofPerm_atom, Equiv.swap_apply_right]

/-- The identity automorphism maps to the identity permutation, so the correspondence is a
group homomorphism and not only a bijection. -/
example : toPerm (1 : MulAut FormalProd) = 1 := autEquivPerm.map_one

/-- Atoms are exactly the irreducibles, checked on a composite: `p₀³ · p₂` is not irreducible. -/
example : ¬ Irreducible example40 := by
  rw [irreducible_iff_isPrimeElt]
  intro h
  rw [← degree_eq_one_iff] at h
  simp [example40] at h

/-! ## Agreement with `riemannZeta`

The statement of `ZetaRigidity/Zeta.lean` checked against the intended valuation, so the version
phrased with Mathlib's `riemannZeta` is not vacuous. -/

example {k : ℕ} (hk : 2 ≤ k) :
    ((∑' m : FormalProd, primeVal.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k :=
  primeVal_agrees_riemannZeta hk

/-! ## The counterexample of `ZetaRigidity/Sharpness.lean`

`badTwo` reproduces `ζ(2)` and differs from the primes. These examples record where it
differs. -/

/-- The perturbed first value sits strictly between `1` and the true first prime `2`. -/
example : 1 < badFirst ∧ badFirst < 2 := by
  refine ⟨one_lt_badFirst, ?_⟩
  nlinarith [badFirst_sq, badFirst_pos]

/-- It is not `2`, which is why `badTwo` is not ζ-normalized. -/
example : badTwo 0 ≠ 2 := by
  rw [badTwo_zero]
  intro h
  have := badFirst_sq
  rw [h] at this
  norm_num at this

/-- The second value is moved up, compensating for the first being moved down. -/
example : badTwo 1 = 4 := badTwo_one

/-- From the third prime on, nothing is changed. -/
example : badTwo 2 = 5 := by
  simp [badTwo, Nat.nth_prime_two_eq_five]

/-- Peeling is inverse to reassembling, on a concrete product: `p₀³ · p₂` has first exponent `3`
and tail `p₁` (the third prime becomes the second after shifting down). -/
example : peelEquiv example40 = (3, atom 1) := by
  refine Prod.ext ?_ ?_
  · simp [example40]
  · refine ext_expo fun i => ?_
    rcases i with _ | _ | j <;> simp [example40]

/-! ## The universal property

`lift` (`ZetaRigidity/Primes.lean`) prescribes a homomorphism by its values on the atoms. -/

example : lift (fun i => (Nat.nth Nat.Prime i : ℝ)) example40 = 40 := by
  rw [example40, map_mul, map_pow, lift_atom, lift_atom,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
  norm_num

end ZetaRigidity

/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Order
import ZetaRigidity.Zeta
import ZetaRigidity.Automorphisms
import ZetaRigidity.Sharpness
import ZetaRigidity.Addition
import ZetaRigidity.EulerProduct
import ZetaRigidity.Characters
import ZetaRigidity.LogIndependence

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

/-! ## The symmetry group of the bare monoid

Sanity checks on `ZetaRigidity/Automorphisms.lean`. These confirm the correspondence is not
degenerate: it is not constantly the identity, and it respects the group structure on both sides.
-/

/-- A transposition of the primes really does move `atom 0` onto `atom 1`. Without the ζ
condition there is nothing to prevent this. -/
example : ofPerm (Equiv.swap 0 1) (atom 0) = atom 1 := by
  rw [ofPerm_atom, Equiv.swap_apply_left]

example : ofPerm (Equiv.swap 0 1) (atom 1) = atom 0 := by
  rw [ofPerm_atom, Equiv.swap_apply_right]

/-- The identity automorphism is the identity permutation -- the correspondence is a group
homomorphism, not merely a bijection of underlying sets. -/
example : toPerm (1 : MulAut FormalProd) = 1 := autEquivPerm.map_one

/-- Atoms are exactly the irreducibles, checked on a composite: `p₀³ · p₂` is not irreducible. -/
example : ¬ Irreducible example40 := by
  rw [irreducible_iff_isPrimeElt]
  intro h
  rw [← degree_eq_one_iff] at h
  simp [example40] at h

/-! ## ζ really is `riemannZeta`

The bridge of `ZetaRigidity/Zeta.lean`, checked against the intended valuation: the theorem
phrased with Mathlib's `riemannZeta` is not vacuous. -/

example {k : ℕ} (hk : 2 ≤ k) :
    ((∑' m : FormalProd, primeVal.extend m ^ (-(k : ℝ)) : ℝ) : ℂ) = riemannZeta k :=
  primeVal_agrees_riemannZeta hk

/-! ## Sharpness: the counterexample is genuinely different

Checks on `ZetaRigidity/Sharpness.lean`. The content is that `badTwo` reproduces `ζ(2)` while
differing from the primes -- so these examples pin down *where* it differs. -/

/-- The perturbed first value sits strictly between `1` and the true first prime `2`. -/
example : 1 < badFirst ∧ badFirst < 2 := by
  refine ⟨one_lt_badFirst, ?_⟩
  nlinarith [badFirst_sq, badFirst_pos]

/-- It is not `2`, which is exactly why `badTwo` is not ζ-normalized. -/
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

/-! ## Addition really is definable

Checks on `ZetaRigidity/Addition.lean`. The identity has to *discriminate*: it must accept
genuine sums and reject near misses, or `add_definable` would be worthless. -/

/-- Accepts a true sum: `2 + 3 = 5`. -/
example : (1 + 2 * 5) * (1 + 3 * 5) = 1 + (1 + 2 * 3) * (5 * 5) := by norm_num

/-- Rejects a near miss: `2 + 3 ≠ 6`, and the identity sees it. -/
example : ¬ ((1 + 2 * 6) * (1 + 3 * 6) = 1 + (1 + 2 * 3) * (6 * 6)) := by norm_num

/-- The successor of the formal product for `40` has value `41`. -/
example : val (msucc example40) = 41 := by rw [val_msucc, val_example]

/-- And the order-theoretic characterisation agrees: nothing sits strictly between `40` and its
successor. This is what makes `msucc` definable from `<` alone. -/
example : MLt example40 (msucc example40) ∧ ∀ r, ¬ (MLt example40 r ∧ MLt r (msucc example40)) :=
  (msucc_eq_iff example40 (msucc example40)).mp rfl

/-! ## The Euler product

Checks on `ZetaRigidity/EulerProduct.lean`. The relabelling `shiftIter` and its range
characterisation are the two places where an off-by-one would silently produce a wrong -- but
still provable-looking -- Euler product, so those are what get tested. -/

/-- Relabelling by `2` sends the first prime to the third. -/
example : shiftIter 2 (atom 0) = atom 2 := by
  refine ext_expo fun i => ?_
  rw [expo_shiftIter]
  rcases i with _ | _ | _ | j <;> simp

example (m : FormalProd) : shiftIter 0 m = m := shiftIter_zero m

/-- `p₀³ · p₂` uses the first prime, so it is *not* in the image of `shiftIter 1`: the image is
exactly the products avoiding `p₀`. -/
example : example40 ∉ Set.range (shiftIter 1) := by
  rw [mem_range_shiftIter]
  intro h
  have := h 0 (by norm_num)
  simp [example40] at this

/-- The atoms from the second prime on *are* in the image. -/
example : atom 3 ∈ Set.range (shiftIter 1) := by
  rw [mem_range_shiftIter]
  intro i hi
  interval_cases i
  simp

/-! ### Divergence

`tendsto_atTop_of_summable` derives Beurling's axiom `p_k → ∞` rather than assuming it. The
negative example is the one that carries the information: a `Valuation` need not diverge on its
own, so the summability hypothesis really is doing the work. -/

example : Filter.Tendsto primeVal Filter.atTop Filter.atTop :=
  primeVal.tendsto_atTop_of_summable (by norm_num) primeVal_summable

/-- A perfectly legal `Valuation` whose values stay below `2`. It is not a Beurling prime
system, which is why divergence has to be derived from convergence of the series and cannot be
read off the `Valuation` axioms. -/
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

/-! ## The universal property and the character group

Checks on `lift`/`hom_ext` (`ZetaRigidity/Primes.lean`) and `ZetaRigidity/Characters.lean`. -/

/-- `lift` computes: prescribing the ordinary primes and extending freely gives `40` on
`p₀³ · p₂`, matching `extend_example` which goes through `Valuation.extend`. -/
example : lift (fun i => (Nat.nth Nat.Prime i : ℝ)) example40 = 40 := by
  rw [example40, map_mul, map_pow, lift_atom, lift_atom,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
  norm_num

/-- The dual correspondence is a group isomorphism, so it fixes the trivial character. -/
example : charEquivTorus 1 = 1 := charEquivTorus.map_one

example (z : ℕ → Circle) : charEquivTorus (charEquivTorus.symm z) = z :=
  charEquivTorus.apply_symm_apply z

/-- And it is not constantly trivial: `signChar` sits at `-1` in the first coordinate. -/
example : charEquivTorus signChar 0 = Circle.exp Real.pi := signChar_atom_zero

/-! ## The primes are a basis

Checks on `ZetaRigidity/LogIndependence.lean`. The first is the one with teeth: no nonzero
integer relation holds among `log 2`, `log 3`, `log 5`. The second confirms the theorem is not
vacuously true of all logarithms — for non-primes, relations do exist. -/

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

/-- Primality is doing the work: `log 2` and `log 4` *are* dependent. -/
example : 2 * Real.log 2 - Real.log 4 = 0 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

end ZetaRigidity

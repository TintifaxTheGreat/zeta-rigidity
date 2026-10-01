/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Rigidity
import ZetaRigidity.Model

/-!
# Sharpness: agreement at one point is not enough

The rigidity theorem requires the Dirichlet series to match ζ at *every* integer `≥ 2`. This file
shows the requirement is not decorative: agreement at `s = 2` alone leaves the valuation free.

## Main results

* `peelEquiv` -- the splitting `FormalProd ≃ ℕ × FormalProd`: a formal product is the exponent of
  the first prime together with everything else, shifted down. This is the Euler-product
  decomposition, stated one prime at a time; `ZetaRigidity/EulerProduct.lean` iterates it to the
  end and gets `ζ_P(s) = ∏_p (1 - p^{-s})⁻¹`.
* `tsum_peel` -- the Dirichlet sum factors accordingly, into a geometric series and the sum for
  the shifted valuation.
* `badTwo_tsum_eq_primeVal_tsum` / `badTwo_not_isZetaNormalized` -- a valuation that is *not* the
  primes and yet reproduces `ζ(2)` exactly.
* `exists_not_isZetaNormalized_agreeing_at_two` -- the two packaged as the sharpness statement.

## The counterexample

Two degrees of freedom are needed. Any single-parameter rescaling of one prime moves the sum
strictly monotonically, so it meets `ζ(2)` only at the intended value; the perturbation has to
give back at one prime what it takes at another. So move the first prime from `2` down to
`√(45/13) ≈ 1.861` and the second from `3` up to `4`, leaving `5, 7, 11, …` alone. The two
Euler factors then satisfy

    (1 - 13/45)⁻¹ · (1 - 1/16)⁻¹  =  45/32 · 16/15  =  3/2  =  4/3 · 9/8
                                  =  (1 - 1/4)⁻¹ · (1 - 1/9)⁻¹

so the perturbed series has the same value at `s = 2`. The remaining factor is never computed --
it is literally the same tsum on both sides, because the two valuations agree from the third
prime on.
-/

namespace ZetaRigidity

open Filter

/-! ## Shifting a valuation -/

/-- Forget the first prime: `v.shift i` is the value of the `(i+1)`-st prime. -/
noncomputable def Valuation.shift (v : Valuation) : Valuation where
  toFun i := v (i + 1)
  one_lt' i := v.one_lt _
  strictMono' _ _ h := v.strictMono (by omega)

@[simp] lemma Valuation.shift_apply (v : Valuation) (i : ℕ) : v.shift i = v (i + 1) := rfl

/-- `extend` only reads the values of the valuation, so pointwise-equal valuations extend to the
same function. This is what lets the two sides of the counterexample share a tail. -/
lemma Valuation.extend_congr {v w : Valuation} (h : ∀ i, v i = w i) (m : FormalProd) :
    v.extend m = w.extend m :=
  Finsupp.prod_congr fun i _ => by rw [h i]

/-! ## Peeling off the first prime

`shiftProd` relabels the primes upwards and `tailProd` undoes it, so every formal product splits
uniquely as a power of the first prime times a product in the remaining primes.
-/

/-- Relabel every prime upwards: `atom i ↦ atom (i + 1)`. -/
noncomputable def shiftProd : FormalProd →* FormalProd where
  toFun m := Multiplicative.ofAdd (Finsupp.mapDomain Nat.succ (Multiplicative.toAdd m))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change Finsupp.mapDomain Nat.succ 0 = 0
    exact Finsupp.mapDomain_zero
  map_mul' m n := by
    apply Multiplicative.toAdd.injective
    change Finsupp.mapDomain Nat.succ (Multiplicative.toAdd m + Multiplicative.toAdd n) = _
    exact Finsupp.mapDomain_add

@[simp] lemma expo_shiftProd_zero (m : FormalProd) : expo (shiftProd m) 0 = 0 := by
  change Finsupp.mapDomain Nat.succ (Multiplicative.toAdd m) 0 = 0
  rw [Finsupp.mapDomain_of_notMem_range]
  simp

@[simp] lemma expo_shiftProd_succ (m : FormalProd) (i : ℕ) :
    expo (shiftProd m) (i + 1) = expo m i := by
  exact Finsupp.mapDomain_apply_of_injective Nat.succ_injective _ i

/-- The point of `shiftProd`: relabelling the primes upwards is the same as shifting the
valuation downwards. -/
lemma extend_shiftProd (v : Valuation) (m : FormalProd) :
    v.extend (shiftProd m) = v.shift.extend m :=
  Finsupp.prod_mapDomain_index_inj Nat.succ_injective

/-- Everything but the first prime, relabelled back down. -/
noncomputable def tailProd (m : FormalProd) : FormalProd :=
  Multiplicative.ofAdd
    (Finsupp.comapDomain Nat.succ (Multiplicative.toAdd m) Nat.succ_injective.injOn)

@[simp] lemma expo_tailProd (m : FormalProd) (i : ℕ) : expo (tailProd m) i = expo m (i + 1) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- **Unique factorisation, in the form the Euler product needs.** Every formal product is a
power of the first prime times a product in the others. -/
lemma atom_pow_mul_shiftProd_tailProd (m : FormalProd) :
    atom 0 ^ expo m 0 * shiftProd (tailProd m) = m := by
  refine ext_expo fun i => ?_
  cases i with
  | zero => simp [expo_mul, expo_pow]
  | succ j => simp [expo_mul, expo_pow]

/-- **The splitting.** A formal product is its first-prime exponent together with the rest. -/
noncomputable def peelEquiv : FormalProd ≃ ℕ × FormalProd where
  toFun m := (expo m 0, tailProd m)
  invFun p := atom 0 ^ p.1 * shiftProd p.2
  left_inv := atom_pow_mul_shiftProd_tailProd
  right_inv := by
    rintro ⟨a, m⟩
    refine Prod.ext ?_ ?_
    · simp [expo_mul, expo_pow]
    · refine ext_expo fun i => ?_
      simp [expo_mul, expo_pow]

@[simp] lemma peelEquiv_apply (m : FormalProd) : peelEquiv m = (expo m 0, tailProd m) := rfl

@[simp] lemma peelEquiv_symm_apply (a : ℕ) (m : FormalProd) :
    peelEquiv.symm (a, m) = atom 0 ^ a * shiftProd m := rfl

/-- The value of a formal product, in split form. -/
lemma extend_peelEquiv_symm (v : Valuation) (a : ℕ) (m : FormalProd) :
    v.extend (peelEquiv.symm (a, m)) = v 0 ^ a * v.shift.extend m := by
  rw [peelEquiv_symm_apply, map_mul, map_pow, v.extend_atom, extend_shiftProd]

/-! ## The Euler factor

With the splitting in place the Dirichlet sum factors into a geometric series in the first prime
and the Dirichlet sum of the shifted valuation. Both directions are needed: one to *compute* the
counterexample's sum, the other to know it converges at all.
-/

variable {v : Valuation} {s : ℝ}

/-- The geometric ratio attached to the first prime. -/
lemma rpow_pow_eq_pow_rpow (v : Valuation) (s : ℝ) (a : ℕ) :
    ((v 0 ^ a : ℝ)) ^ (-s) = ((v 0 ^ (-s) : ℝ)) ^ a := by
  rw [← Real.rpow_natCast (v 0) a, ← Real.rpow_natCast ((v 0) ^ (-s)) a,
    ← Real.rpow_mul (v.pos 0).le, ← Real.rpow_mul (v.pos 0).le, mul_comm]

/-- The summand, in split coordinates. -/
lemma peel_summand (v : Valuation) (s : ℝ) (p : ℕ × FormalProd) :
    v.extend (peelEquiv.symm p) ^ (-s)
      = ((v 0 ^ (-s) : ℝ)) ^ p.1 * v.shift.extend p.2 ^ (-s) := by
  obtain ⟨a, m⟩ := p
  rw [extend_peelEquiv_symm, Real.mul_rpow (pow_nonneg (v.pos 0).le a) (v.shift.extend_pos m).le,
    rpow_pow_eq_pow_rpow]

/-- The geometric series of the first Euler factor converges exactly when the first prime has
value `> 1` in the relevant range -- which it does, for every `s > 0`. -/
lemma summable_euler_factor (v : Valuation) (hs : 0 < s) :
    Summable fun a : ℕ => ((v 0 ^ (-s) : ℝ)) ^ a := by
  refine summable_geometric_of_lt_one (Real.rpow_nonneg (v.pos 0).le _) ?_
  rw [Real.rpow_neg (v.pos 0).le, inv_lt_one_iff₀]
  exact Or.inr (Real.one_lt_rpow_iff_of_pos (v.pos 0) |>.mpr (Or.inl ⟨v.one_lt 0, hs⟩))

/-- **Peeling preserves summability downwards.** -/
lemma Summable.peel (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Summable fun m : FormalProd => v.shift.extend m ^ (-s) := by
  have hprod : Summable fun p : ℕ × FormalProd => v.extend (peelEquiv.symm p) ^ (-s) :=
    (peelEquiv.symm.summable_iff (f := fun m : FormalProd => v.extend m ^ (-s))).mpr h
  have h0 := hprod.prod_factor 0
  refine h0.congr fun m => ?_
  rw [peel_summand]
  simp

/-- **Peeling preserves summability upwards.** This is the direction that establishes the
counterexample converges: it never mentions the original valuation's sum. -/
lemma summable_of_peel (hs : 0 < s)
    (h : Summable fun m : FormalProd => v.shift.extend m ^ (-s)) :
    Summable fun m : FormalProd => v.extend m ^ (-s) := by
  refine (peelEquiv.symm.summable_iff (f := fun m : FormalProd => v.extend m ^ (-s))).mp ?_
  refine Summable.congr ((summable_euler_factor v hs).mul_of_nonneg h ?_ ?_) fun p => ?_
  · exact fun a => pow_nonneg (Real.rpow_nonneg (v.pos 0).le _) a
  · exact fun m => Real.rpow_nonneg (v.shift.extend_pos m).le _
  · exact (peel_summand v s p).symm

/-- **The Euler factorization, one prime at a time.** -/
theorem tsum_peel (hs : 0 < s) (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    ∑' m : FormalProd, v.extend m ^ (-s)
      = (∑' a : ℕ, ((v 0 ^ (-s) : ℝ)) ^ a) * ∑' m : FormalProd, v.shift.extend m ^ (-s) := by
  rw [tsum_mul_tsum_of_summable_norm (f := fun a : ℕ => ((v 0 ^ (-s) : ℝ)) ^ a)
    (g := fun m : FormalProd => v.shift.extend m ^ (-s)) ?_ ?_]
  · rw [← peelEquiv.symm.tsum_eq (fun m : FormalProd => v.extend m ^ (-s))]
    exact tsum_congr fun p => peel_summand v s p
  · refine (summable_euler_factor v hs).congr fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.rpow_nonneg (v.pos 0).le _) a)]
  · refine (Summable.peel h).congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (v.shift.extend_pos m).le _)]

/-- The Euler factor, evaluated: a geometric series. -/
lemma tsum_euler_factor (v : Valuation) (hs : 0 < s) :
    (∑' a : ℕ, ((v 0 ^ (-s) : ℝ)) ^ a) = (1 - v 0 ^ (-s))⁻¹ := by
  refine tsum_geometric_of_lt_one (Real.rpow_nonneg (v.pos 0).le _) ?_
  rw [Real.rpow_neg (v.pos 0).le, inv_lt_one_iff₀]
  exact Or.inr (Real.one_lt_rpow_iff_of_pos (v.pos 0) |>.mpr (Or.inl ⟨v.one_lt 0, hs⟩))

/-- Everything below runs at `s = 2`, where the negative real power is an ordinary square. -/
private lemma rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- Peeling twice, with the two Euler factors evaluated. -/
lemma tsum_peel_two (v : Valuation) (h : Summable fun m : FormalProd => v.extend m ^ (-(2 : ℝ))) :
    ∑' m : FormalProd, v.extend m ^ (-(2 : ℝ))
      = (1 - (v 0 ^ 2)⁻¹)⁻¹ * (1 - (v 1 ^ 2)⁻¹)⁻¹
        * ∑' m : FormalProd, v.shift.shift.extend m ^ (-(2 : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [tsum_peel h2 h, tsum_euler_factor v h2, tsum_peel h2 (Summable.peel h),
    tsum_euler_factor v.shift h2, rpow_neg_two (v.pos 0), rpow_neg_two (v.shift.pos 0)]
  rw [Valuation.shift_apply]
  ring

/-! ## The counterexample

`badFirst = √(45/13) ≈ 1.861` replaces the prime `2`, and `4` replaces the prime `3`. The choice
is forced by wanting the two Euler factors to multiply to `3/2`, which is what `2` and `3`
contribute; `45/13` is the solution of `(1 - 1/x)⁻¹ · 16/15 = 3/2`.
-/

/-- The perturbed value of the first prime. -/
noncomputable def badFirst : ℝ := Real.sqrt (45 / 13)

@[simp] lemma badFirst_sq : badFirst ^ 2 = 45 / 13 := Real.sq_sqrt (by norm_num)

lemma badFirst_pos : 0 < badFirst := Real.sqrt_pos.mpr (by norm_num)

lemma one_lt_badFirst : 1 < badFirst := by
  nlinarith [badFirst_sq, badFirst_pos]

lemma badFirst_lt_four : badFirst < 4 := by
  nlinarith [badFirst_sq, badFirst_pos]

/-- **A valuation that is not the primes but has the right value at `s = 2`.** It sends the first
prime to `√(45/13)`, the second to `4`, and every later prime to itself. -/
noncomputable def badTwo : Valuation where
  toFun i := if i = 0 then badFirst else if i = 1 then 4 else (Nat.nth Nat.Prime i : ℝ)
  one_lt' i := by
    rcases i with _ | _ | j
    · simpa using one_lt_badFirst
    · norm_num
    · simp only [Nat.succ_ne_zero, ite_false]
      exact_mod_cast (nth_prime_prime (j + 2)).one_lt
  strictMono' := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    rcases i with _ | _ | j
    · simpa using badFirst_lt_four
    · simp only [reduceIte]
      rw [show Nat.nth Nat.Prime 2 = 5 from Nat.nth_prime_two_eq_five]
      norm_num
    · simp only [Nat.succ_ne_zero, ite_false]
      exact_mod_cast Nat.nth_strictMono primes_infinite (Nat.lt_succ_self (j + 2))

@[simp] lemma badTwo_zero : badTwo 0 = badFirst := rfl
@[simp] lemma badTwo_one : badTwo 1 = 4 := rfl

lemma badTwo_shift_shift (i : ℕ) : badTwo.shift.shift i = primeVal.shift.shift i := by
  change badTwo (i + 2) = (Nat.nth Nat.Prime (i + 2) : ℝ)
  simp [badTwo]

/-- The two valuations share everything from the third prime on, so the un-evaluated tail of the
Euler product is literally the same object on both sides. -/
lemma tsum_tail_eq :
    (∑' m : FormalProd, badTwo.shift.shift.extend m ^ (-(2 : ℝ)))
      = ∑' m : FormalProd, primeVal.shift.shift.extend m ^ (-(2 : ℝ)) :=
  tsum_congr fun m => by rw [Valuation.extend_congr badTwo_shift_shift m]

lemma primeVal_summable : Summable fun m : FormalProd => primeVal.extend m ^ (-(2 : ℝ)) := by
  have h := primeVal_isZetaNormalized.summable
  rwa [show (-2 : ℝ) = -(2 : ℝ) by norm_num] at h

lemma badTwo_summable : Summable fun m : FormalProd => badTwo.extend m ^ (-(2 : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  refine summable_of_peel h2 (summable_of_peel h2 ?_)
  refine (Summable.peel (Summable.peel primeVal_summable)).congr fun m => ?_
  rw [Valuation.extend_congr badTwo_shift_shift m]

/-- **The sums agree at `s = 2`.** Neither side's tail is ever computed: the two Euler factors
multiply to `3/2` in both cases, and the remaining factor is shared. -/
theorem badTwo_tsum_eq_primeVal_tsum :
    (∑' m : FormalProd, badTwo.extend m ^ (-(2 : ℝ)))
      = ∑' m : FormalProd, primeVal.extend m ^ (-(2 : ℝ)) := by
  rw [tsum_peel_two badTwo badTwo_summable, tsum_peel_two primeVal primeVal_summable,
    tsum_tail_eq]
  congr 1
  have h0 : primeVal 0 = 2 := by simp [primeVal, Nat.nth_prime_zero_eq_two]
  have h1 : primeVal 1 = 3 := by simp [primeVal, Nat.nth_prime_one_eq_three]
  rw [badTwo_zero, badTwo_one, h0, h1, badFirst_sq]
  norm_num

/-- The counterexample is not ζ-normalized: rigidity would force its first value to be `2`, and
`√(45/13) ≠ 2`. -/
theorem badTwo_not_isZetaNormalized : ¬ IsZetaNormalized badTwo := by
  intro h
  have h0 := eq_nth_prime_of_isZetaNormalized h 0
  rw [Nat.nth_prime_zero_eq_two, badTwo_zero] at h0
  have := badFirst_sq
  rw [h0] at this
  norm_num at this

/-- **Sharpness.** Agreement with ζ at the single point `s = 2` does not force the valuation to
be the primes. The rigidity theorem's use of *every* integer `≥ 2` is therefore essential. -/
theorem exists_not_isZetaNormalized_agreeing_at_two :
    ∃ w : Valuation,
      (Summable fun m : FormalProd => w.extend m ^ (-(2 : ℝ))) ∧
      (∑' m : FormalProd, w.extend m ^ (-(2 : ℝ)))
        = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ)) ∧
      ¬ IsZetaNormalized w := by
  refine ⟨badTwo, badTwo_summable, ?_, badTwo_not_isZetaNormalized⟩
  rw [badTwo_tsum_eq_primeVal_tsum]
  have h := primeVal_isZetaNormalized.agrees 2 le_rfl
  rwa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at h

end ZetaRigidity

/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Sharpness
import ZetaRigidity.Model

/-!
# The Euler product for the Beurling zeta function

`ZetaRigidity/Sharpness.lean` peels one prime off the Dirichlet series. This file iterates that
to the end and proves the defining identity of the subject:

    ζ_P(s) = ∏_p (1 - p^{-s})⁻¹

for an arbitrary `Valuation`, that is for a generalized prime system with distinct primes and
not only for the rational primes.

## Main result

`eulerProduct`, stated as a limit of finite partial products, following the convention of
`EulerProduct.eulerProduct_completely_multiplicative` in Mathlib. That lemma does not apply
here: it is stated for `f : ℕ →*₀ F` over `Nat.primesBelow`, whereas here the primes are
unknown reals.

## Proof outline

Iterating `tsum_peel` `n` times (`tsum_peel_iter`) gives the exact identity

    ζ_P(s) = (∏ i < n, (1 - v i ^ (-s))⁻¹) * A n,     A n := ∑' m, (v.shiftBy n).extend m ^ (-s)

so the theorem reduces to `A n → 1`. That step needs the summability hypothesis. The recursion
`A n = (1 - v n ^ (-s))⁻¹ * A (n+1)` from `tsum_peel` is scale-invariant: it determines the
ratios `A n / A (n+1)` but admits any positive limit, so it gives no bound on its own. The bound
comes from the observation that `A n` is a sum over the formal products using no prime below
`n`, and those sets shrink to `{1}`.
-/

namespace ZetaRigidity

open Filter

variable {v : Valuation} {s : ℝ}

/-! ## Forgetting the first `n` primes -/

/-- The Beurling system with the first `n` primes deleted. -/
noncomputable def Valuation.shiftBy (v : Valuation) (n : ℕ) : Valuation where
  toFun i := v (i + n)
  one_lt' _ := v.one_lt _
  strictMono' _ _ h := v.strictMono (by omega)

@[simp] lemma Valuation.shiftBy_apply (v : Valuation) (n i : ℕ) : v.shiftBy n i = v (i + n) := rfl

lemma Valuation.shiftBy_zero (v : Valuation) (i : ℕ) : v.shiftBy 0 i = v i := by simp

lemma Valuation.shift_shiftBy (v : Valuation) (n i : ℕ) :
    (v.shiftBy n).shift i = v.shiftBy (n + 1) i := by
  simp only [Valuation.shift_apply, Valuation.shiftBy_apply]
  congr 1
  omega

lemma Valuation.shiftBy_shift (v : Valuation) (n i : ℕ) :
    v.shift.shiftBy n i = v.shiftBy (n + 1) i := rfl

/-- Relabel every prime upwards by `n`. -/
noncomputable def shiftIter : ℕ → (FormalProd →* FormalProd)
  | 0 => MonoidHom.id _
  | n + 1 => shiftProd.comp (shiftIter n)

@[simp] lemma shiftIter_zero (m : FormalProd) : shiftIter 0 m = m := rfl

lemma shiftIter_succ (n : ℕ) (m : FormalProd) :
    shiftIter (n + 1) m = shiftProd (shiftIter n m) := rfl

@[simp] lemma expo_shiftIter (n : ℕ) (m : FormalProd) (i : ℕ) :
    expo (shiftIter n m) i = if n ≤ i then expo m (i - n) else 0 := by
  induction n generalizing i with
  | zero => simp
  | succ k ih =>
    rw [shiftIter_succ]
    cases i with
    | zero => simp
    | succ j =>
      rw [expo_shiftProd_succ, ih]
      split_ifs with h1 h2 h2
      · congr 1; omega
      · omega
      · omega
      · rfl

/-- Relabelling the primes upwards by `n` is the same as forgetting the first `n` of them. -/
lemma extend_shiftIter (v : Valuation) (n : ℕ) (m : FormalProd) :
    v.extend (shiftIter n m) = (v.shiftBy n).extend m := by
  induction n generalizing v with
  | zero => exact (Valuation.extend_congr (fun i => (v.shiftBy_zero i).symm) m)
  | succ k ih =>
    rw [shiftIter_succ, extend_shiftProd, ih v.shift]
    exact Valuation.extend_congr (v.shiftBy_shift k) m

/-- Everything above the first `n` primes, relabelled back down. -/
private lemma add_right_injective' (n : ℕ) : Function.Injective (· + n) :=
  fun _ _ h => by simpa using h

noncomputable def tailIter (n : ℕ) (m : FormalProd) : FormalProd :=
  Multiplicative.ofAdd
    (Finsupp.comapDomain (· + n) (Multiplicative.toAdd m) (add_right_injective' n).injOn)

@[simp] lemma expo_tailIter (n : ℕ) (m : FormalProd) (i : ℕ) :
    expo (tailIter n m) i = expo m (i + n) :=
  Finsupp.comapDomain_apply _ _ _ _

lemma shiftIter_injective (n : ℕ) : Function.Injective (shiftIter n) := by
  intro a b hab
  refine ext_expo fun i => ?_
  have h := congrArg (fun m => expo m (i + n)) hab
  simpa using h

/-- The image of `shiftIter n` is the set of formal products using no prime below `n`. This
makes `A n` a sum over a shrinking family of subsets of a fixed index type. -/
lemma mem_range_shiftIter {n : ℕ} {m : FormalProd} :
    m ∈ Set.range (shiftIter n) ↔ ∀ i < n, expo m i = 0 := by
  constructor
  · rintro ⟨m', rfl⟩ i hi
    simp [Nat.not_le.mpr hi]
  · intro h
    refine ⟨tailIter n m, ext_expo fun i => ?_⟩
    rw [expo_shiftIter]
    split_ifs with hi
    · rw [expo_tailIter]
      congr 1
      omega
    · exact (h i (Nat.not_le.mp hi)).symm

/-! ## Iterated peeling -/

lemma summable_shiftBy (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    ∀ n, Summable fun m : FormalProd => (v.shiftBy n).extend m ^ (-s) := by
  intro n
  induction n generalizing v with
  | zero =>
    exact h.congr fun m => by rw [Valuation.extend_congr (fun i => (v.shiftBy_zero i).symm) m]
  | succ k ih =>
    have := ih (v := v.shift) (Summable.peel h)
    exact this.congr fun m => by
      rw [Valuation.extend_congr (v.shiftBy_shift k) m]

/-- Peeling `n` times gives an exact identity: no limit is taken, and `A n` is the remainder. -/
theorem tsum_peel_iter (hs : 0 < s) (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    ∀ n, ∑' m : FormalProd, v.extend m ^ (-s)
      = (∏ i ∈ Finset.range n, (1 - v i ^ (-s))⁻¹)
        * ∑' m : FormalProd, (v.shiftBy n).extend m ^ (-s) := by
  intro n
  induction n with
  | zero =>
    rw [Finset.prod_range_zero, one_mul]
    exact tsum_congr fun m => by
      rw [Valuation.extend_congr (fun i => (v.shiftBy_zero i).symm) m]
  | succ k ih =>
    rw [ih, Finset.prod_range_succ]
    -- Peel one more prime off the remainder.
    have hk := summable_shiftBy h k
    rw [tsum_peel hs hk, tsum_euler_factor (v.shiftBy k) hs, Valuation.shiftBy_apply]
    have hshift : ∑' m : FormalProd, (v.shiftBy k).shift.extend m ^ (-s)
        = ∑' m : FormalProd, (v.shiftBy (k + 1)).extend m ^ (-s) :=
      tsum_congr fun m => by rw [Valuation.extend_congr (v.shift_shiftBy k) m]
    rw [hshift, zero_add]
    ring

/-! ## The remainder tends to `1`

`A n` is the Dirichlet sum of the system with the first `n` primes deleted. On the original
index type it is the sum over formal products using no prime below `n`, and those sets shrink
to `{1}`. Since the full series converges, its tail outside any sufficiently large finite set is
small, which gives `A n → 1`.
-/

/-- The summand with the empty product removed. This does not depend on `n`, so `A n` is a sum
of the same function over a shrinking index set. -/
private noncomputable def tailTerm (v : Valuation) (s : ℝ) (y : FormalProd) : ℝ :=
  if y = 1 then 0 else v.extend y ^ (-s)

private lemma tailTerm_nonneg (v : Valuation) (s : ℝ) (y : FormalProd) : 0 ≤ tailTerm v s y := by
  unfold tailTerm
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (v.extend_pos y) _).le

private lemma tailTerm_le (v : Valuation) (s : ℝ) (y : FormalProd) :
    tailTerm v s y ≤ v.extend y ^ (-s) := by
  unfold tailTerm
  split_ifs
  · exact (Real.rpow_pos_of_pos (v.extend_pos y) _).le
  · exact le_rfl

private lemma summable_tailTerm (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Summable (tailTerm v s) :=
  h.of_nonneg_of_le (tailTerm_nonneg v s) (tailTerm_le v s)

private lemma shiftIter_eq_one_iff {n : ℕ} {m : FormalProd} : shiftIter n m = 1 ↔ m = 1 :=
  ⟨fun h => shiftIter_injective n (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

/-- `A n` is `1` plus a sum of `tailTerm` over the image of `shiftIter n`. -/
private lemma tsum_shiftBy_eq (h : Summable fun m : FormalProd => v.extend m ^ (-s)) (n : ℕ) :
    ∑' m : FormalProd, (v.shiftBy n).extend m ^ (-s)
      = 1 + ∑' m : FormalProd, tailTerm v s (shiftIter n m) := by
  have hre : ∀ m : FormalProd,
      (v.shiftBy n).extend m ^ (-s) = v.extend (shiftIter n m) ^ (-s) := fun m => by
    rw [extend_shiftIter]
  rw [tsum_congr hre]
  have hsplit : ∀ m : FormalProd, v.extend (shiftIter n m) ^ (-s)
      = (if m = 1 then (1 : ℝ) else 0) + tailTerm v s (shiftIter n m) := by
    intro m
    unfold tailTerm
    by_cases hm : m = 1
    · simp [hm, Real.one_rpow]
    · have hne : shiftIter n m ≠ 1 := fun hc => hm (shiftIter_eq_one_iff.mp hc)
      simp [hm, hne]
  rw [tsum_congr hsplit]
  have h1 : Summable fun m : FormalProd => if m = 1 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := ({1} : Finset FormalProd)) fun m hm => by
      simp only [Finset.mem_singleton] at hm
      simp [hm]
  have h2 : Summable fun m : FormalProd => tailTerm v s (shiftIter n m) :=
    (summable_tailTerm h).comp_injective (shiftIter_injective n)
  rw [h1.tsum_add h2, tsum_ite_eq]

/-- Any fixed finite set of formal products is eventually disjoint from the image of
`shiftIter n`, apart from the empty product. -/
private lemma eventually_disjoint_range (F : Finset FormalProd) :
    ∃ N, ∀ n ≥ N, ∀ y ∈ F, y ≠ 1 → y ∉ Set.range (shiftIter n) := by
  refine ⟨(F.sup fun y => (Multiplicative.toAdd y).support.sup id) + 1,
    fun n hn y hy hy1 hmem => ?_⟩
  obtain ⟨i, hi⟩ := exists_expo_pos hy1
  have hisupp : i ∈ (Multiplicative.toAdd y).support := Finsupp.mem_support_iff.mpr hi.ne'
  have h1 : i ≤ (Multiplicative.toAdd y).support.sup id := Finset.le_sup (f := id) hisupp
  have h2 : (Multiplicative.toAdd y).support.sup id
      ≤ F.sup fun z => (Multiplicative.toAdd z).support.sup id :=
    Finset.le_sup (f := fun z => (Multiplicative.toAdd z).support.sup id) hy
  exact absurd (mem_range_shiftIter.mp hmem i (by omega)) hi.ne'

/-- The remainder tends to `1`. -/
theorem tendsto_tsum_shiftBy (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Tendsto (fun n => ∑' m : FormalProd, (v.shiftBy n).extend m ^ (-s)) atTop (nhds 1) := by
  have hT := summable_tailTerm h
  have hgoal :
      Tendsto (fun n => ∑' m : FormalProd, tailTerm v s (shiftIter n m)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- A finite set carrying all but `ε` of the series.
    obtain ⟨F, hF⟩ :=
      (Metric.tendsto_atTop.mp (tendsto_tsum_compl_atTop_zero (tailTerm v s))) ε hε
    obtain ⟨N, hN⟩ := eventually_disjoint_range F
    refine ⟨N, fun n hn => ?_⟩
    have hinj := shiftIter_injective n
    have hsummand : Summable fun m : FormalProd => tailTerm v s (shiftIter n m) :=
      hT.comp_injective hinj
    -- Discard the `m = 1` term, which is zero, so the remaining map avoids `F`.
    have hsupp : ∑' m : ({m : FormalProd | m ≠ 1} : Set FormalProd),
          tailTerm v s (shiftIter n m.1)
        = ∑' m : FormalProd, tailTerm v s (shiftIter n m) :=
      tsum_subtype_eq_of_support_subset
        (f := fun y : FormalProd => tailTerm v s (shiftIter n y))
        (s := {m : FormalProd | m ≠ 1}) (by
          intro m hm
          change m ≠ 1
          rintro rfl
          exact hm (show tailTerm v s (shiftIter n 1) = 0 by rw [map_one]; simp [tailTerm]))
    have hle : ∑' m : FormalProd, tailTerm v s (shiftIter n m)
        ≤ ∑' y : {x : FormalProd // x ∉ F}, tailTerm v s y := by
      rw [← hsupp]
      refine Summable.tsum_le_tsum_of_inj
        (fun m => (⟨shiftIter n m.1, fun hmem =>
          hN n hn _ hmem (fun hc => m.2 (shiftIter_eq_one_iff.mp hc)) ⟨m.1, rfl⟩⟩ :
            {x : FormalProd // x ∉ F}))
        (fun a b hab => Subtype.ext (hinj (Subtype.ext_iff.mp hab)))
        (fun c _ => tailTerm_nonneg v s c) (fun _ => le_rfl)
        (hsummand.subtype _) (hT.subtype _)
    have hnonneg : 0 ≤ ∑' m : FormalProd, tailTerm v s (shiftIter n m) :=
      tsum_nonneg fun m => tailTerm_nonneg v s _
    have hFlt := hF F le_rfl
    rw [Real.dist_eq, sub_zero] at hFlt ⊢
    calc |∑' m : FormalProd, tailTerm v s (shiftIter n m)|
        = ∑' m : FormalProd, tailTerm v s (shiftIter n m) := abs_of_nonneg hnonneg
      _ ≤ ∑' y : {x : FormalProd // x ∉ F}, tailTerm v s y := hle
      _ ≤ |∑' y : {x : FormalProd // x ∉ F}, tailTerm v s y| := le_abs_self _
      _ < ε := hFlt
  have hlim := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add hgoal
  rw [add_zero] at hlim
  exact hlim.congr fun n => (tsum_shiftBy_eq h n).symm

/-- The remainder is at least `1`, because the empty product contributes `1`. -/
lemma one_le_tsum_shiftBy (h : Summable fun m : FormalProd => v.extend m ^ (-s)) (n : ℕ) :
    1 ≤ ∑' m : FormalProd, (v.shiftBy n).extend m ^ (-s) := by
  rw [tsum_shiftBy_eq h n]
  have : 0 ≤ ∑' m : FormalProd, tailTerm v s (shiftIter n m) :=
    tsum_nonneg fun m => tailTerm_nonneg v s _
  linarith

/-! ## The Euler product -/

/-- The Euler product for the zeta function of a generalized prime system.

    ζ_P(s) = ∏_p (1 - p^{-s})⁻¹

stated as the limit of the partial products over the first `n` primes, as in
`EulerProduct.eulerProduct_completely_multiplicative`. Unlike that lemma this holds for an
arbitrary `Valuation`, where the primes are unknown reals rather than `Nat.primesBelow`. -/
theorem eulerProduct (hs : 0 < s) (h : Summable fun m : FormalProd => v.extend m ^ (-s)) :
    Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - v i ^ (-s))⁻¹) atTop
      (nhds (∑' m : FormalProd, v.extend m ^ (-s))) := by
  set S := ∑' m : FormalProd, v.extend m ^ (-s) with hS
  set A := fun n => ∑' m : FormalProd, (v.shiftBy n).extend m ^ (-s) with hA
  have hAne : ∀ n, A n ≠ 0 := fun n => by
    have := one_le_tsum_shiftBy h n
    rw [hA]
    linarith
  -- Peeling is exact, so the partial product is `S / A n`.
  have hquot : ∀ n, (∏ i ∈ Finset.range n, (1 - v i ^ (-s))⁻¹) = S / A n := by
    intro n
    rw [eq_div_iff (hAne n), hS]
    exact (tsum_peel_iter hs h n).symm
  have hdiv : Tendsto (fun n => S / A n) atTop (nhds (S / 1)) :=
    tendsto_const_nhds.div (tendsto_tsum_shiftBy h) one_ne_zero
  rw [div_one] at hdiv
  exact hdiv.congr fun n => (hquot n).symm

/-! ## Non-vacuity

Instantiating at the intended model recovers the classical Euler product for `ζ(2)`. The
argument above never mentions the rational primes, so this tests the whole chain rather than
restating a definition.
-/

/-- The classical Euler product at `s = 2`, as an instance of `eulerProduct`. -/
theorem primeVal_eulerProduct :
    Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - (Nat.nth Nat.Prime i : ℝ) ^ (-(2 : ℝ)))⁻¹)
      atTop (nhds (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(2 : ℝ)))) := by
  have h := eulerProduct (v := primeVal) (s := 2) (by norm_num) primeVal_summable
  have hzeta : ∑' m : FormalProd, primeVal.extend m ^ (-(2 : ℝ))
      = ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(2 : ℝ)) := by
    have hag := primeVal_isZetaNormalized.agrees 2 le_rfl
    rwa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hag
  rwa [hzeta] at h

end ZetaRigidity

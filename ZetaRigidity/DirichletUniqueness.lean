/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import Mathlib

/-!
# Uniqueness for power sums

A family of reals in `(0, 1]` is determined, as a multiset, by its power sums `∑ᵢ xᵢ ⁿ` for
`n ≥ 2`. This is the analytic engine of the ζ-rigidity theorem.

## Why natural powers

The ζ-hypothesis is imposed only at the integer arguments `s = 2, 3, 4, …`, so substituting
`xᵢ = (value)⁻¹` turns the Dirichlet series into ordinary power sums. That removes `Real.rpow`
from the whole argument, which matters in practice: `Monoid.npow` has far better `simp`, `gcongr`
and `positivity` support. `ZetaRigidity/Rigidity.lean` does the conversion with
`rpow_neg_natCast_eq_inv_pow`.

## Why this cannot be taken from Mathlib

`Mathlib/NumberTheory/LSeries/Injectivity.lean` runs exactly this argument
(`LSeries.tendsto_cpow_mul_atTop`: the dominant term dominates as `s → ∞`), but only for series
indexed by `ℕ` whose exponents *are* the index. Here the values are unknown -- determining them
is the theorem -- so that file is a template to imitate, not a result to apply.

## Contents

* local finiteness, which gives the multiset of values a greatest element;
* `exists_equiv_of_mult_eq` -- equal multiplicities assemble fibrewise into a bijection;
* `tendsto_tsum_pow` -- the dominant term dominates: power sums converge to the multiplicity
  of the largest value;
* `mult_eq_mult` -- equal power sums force equal multiplicities, by minimal counterexample;
* `exists_equiv_of_tsum_pow_eq` -- the theorem used downstream.

Complete, with no `sorry`.
-/

namespace ZetaRigidity

open Filter

/-! ## Local finiteness

Summability makes the value family locally finite, which is what gives the multiset of values a
least element -- the hook the whole argument hangs on.
-/

/-- A summable family exceeds any positive threshold only finitely often. -/
theorem finite_above {ι : Type*} {g : ι → ℝ} (hg : Summable g) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ g i}.Finite :=
  (Filter.eventually_cofinite.mp
    (Filter.Tendsto.eventually_lt_const hε hg.tendsto_cofinite_zero)).subset
      fun _ hi => not_lt.mpr hi

/-- Only finitely many members of the family are at least `c`, for `c > 0`. -/
theorem finite_ge {ι : Type*} {x : ι → ℝ} (hxs : Summable fun i => x i ^ 2) {c : ℝ} (hc : 0 < c) :
    {i | c ≤ x i}.Finite := by
  refine (finite_above hxs (ε := c ^ 2) (by positivity)).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi ⊢
  gcongr

/-- Each value is attained only finitely often. -/
theorem finite_fiber {ι : Type*} {x : ι → ℝ} (hxs : Summable fun i => x i ^ 2) {c : ℝ}
    (hc : 0 < c) : {i | x i = c}.Finite :=
  (finite_ge hxs hc).subset fun _ hi => le_of_eq hi.symm

/-! ## Multiplicities -/

/-- The multiplicity with which the family `x` attains the value `c`. -/
noncomputable def mult {ι : Type*} (x : ι → ℝ) (c : ℝ) : ℕ := Nat.card {i // x i = c}

/-! ## Fibrewise assembly -/

/-- Two families attaining each value with the same finite multiplicity differ only by a
relabelling. The bijection is assembled fibrewise: decompose each index type as a sigma over
values, match fibres of equal size, and reassemble. -/
theorem exists_equiv_of_mult_eq {ι κ : Type*} {x : ι → ℝ} {y : κ → ℝ}
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ k, 0 < y k)
    (hfx : ∀ c, 0 < c → {i | x i = c}.Finite) (hfy : ∀ c, 0 < c → {k | y k = c}.Finite)
    (h : ∀ c, 0 < c → mult x c = mult y c) :
    ∃ e : ι ≃ κ, ∀ i, x i = y (e i) := by
  -- A value-preserving bijection of fibres, for every real `c`.
  have fib : ∀ c : ℝ, {i // x i = c} ≃ {k // y k = c} := by
    intro c
    by_cases hc : 0 < c
    · -- Both fibres are finite of the same size.
      have f1 : Finite {i // x i = c} := (hfx c hc).to_subtype
      have f2 : Finite {k // y k = c} := (hfy c hc).to_subtype
      have := Fintype.ofFinite {i // x i = c}
      have := Fintype.ofFinite {k // y k = c}
      exact Fintype.equivOfCardEq (by simpa [mult, Nat.card_eq_fintype_card] using h c hc)
    · -- No value is `≤ 0`, so both fibres are empty.
      have e1 : IsEmpty {i // x i = c} := ⟨fun p => hc (p.2 ▸ hx0 p.1)⟩
      have e2 : IsEmpty {k // y k = c} := ⟨fun p => hc (p.2 ▸ hy0 p.1)⟩
      exact Equiv.equivOfIsEmpty _ _
  refine ⟨(Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight fib).trans (Equiv.sigmaFiberEquiv y)), fun i => ?_⟩
  exact ((fib (x i)) ⟨i, rfl⟩).2.symm

/-! ## The dominant term

As `n → ∞` the power sum `∑ᵢ zᵢ ⁿ` of a family in `(0, 1]` forgets everything except how often
the value `1` is attained: every smaller value is crushed. This is the engine of the argument,
and the rescaled form (divide a family by its largest value) is how multiplicities get read off.
-/

/-- A family taking the value `1` finitely often sums its indicator to that count. -/
theorem tsum_indicator_eq_card {ι : Type*} {z : ι → ℝ} (hA : {i | z i = 1}.Finite) :
    ∑' i, (if z i = 1 then (1 : ℝ) else 0) = Nat.card {i // z i = 1} := by
  classical
  have hzero : ∀ b ∉ hA.toFinset, (if z b = 1 then (1 : ℝ) else 0) = 0 := by
    intro b hb
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hb
    simp [hb]
  have hone : ∀ i ∈ hA.toFinset, (if z i = 1 then (1 : ℝ) else 0) = 1 := by
    intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
    simp [hi]
  have hcard : Nat.card {i // z i = 1} = hA.toFinset.card := Set.ncard_eq_toFinset_card _ hA
  rw [tsum_eq_sum hzero, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
    hcard]

/-- **The dominant term dominates.** For a family in `(0, 1]` with summable squares, the power
sums converge to the multiplicity of the value `1`. Proved by Tannery's theorem: `zᵢ ^ 2`
dominates `zᵢ ^ n` for `n ≥ 2`, and pointwise `zᵢ ^ n → 1` or `0` according as `zᵢ = 1`. -/
theorem tendsto_tsum_pow {ι : Type*} {z : ι → ℝ} (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i ≤ 1)
    (hs : Summable fun i => z i ^ 2) :
    Tendsto (fun n : ℕ => ∑' i, z i ^ n) atTop (nhds (Nat.card {i // z i = 1})) := by
  have hpt : ∀ i, Tendsto (fun n : ℕ => z i ^ n) atTop (nhds (if z i = 1 then (1 : ℝ) else 0)) := by
    intro i
    by_cases h : z i = 1
    · simp [h]
    · have hlt : z i < 1 := lt_of_le_of_ne (hz1 i) h
      simpa [h] using tendsto_pow_atTop_nhds_zero_of_lt_one (hz0 i).le hlt
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ‖z i ^ n‖ ≤ z i ^ 2 := by
    filter_upwards [eventually_ge_atTop 2] with n hn i
    rw [Real.norm_of_nonneg (pow_nonneg (hz0 i).le n)]
    exact pow_le_pow_of_le_one (hz0 i).le (hz1 i) hn
  have key := tendsto_tsum_of_dominated_convergence hs hpt hbound
  rwa [tsum_indicator_eq_card (finite_fiber hs one_pos)] at key

/-! ## Scaffolding for the remaining gap

The plan for `mult_eq_mult` is a minimal counterexample. These are its moving parts: the
disagreement set has a greatest element (`exists_max`, fed by `finite_values_above`), and above
that element the two families are related by a value-preserving bijection
(`exists_equiv_above`), so their "head" sums agree and can be subtracted.
-/

/-- A positive multiplicity means the value really is attained. -/
theorem exists_eq_of_mult_pos {ι : Type*} {x : ι → ℝ} {c : ℝ} (h : 0 < mult x c) :
    ∃ i, x i = c := by
  rw [mult, Nat.card_pos_iff] at h
  exact ⟨h.1.some.1, h.1.some.2⟩

/-- Only finitely many *values* are attained at or above a positive bound. -/
theorem finite_values_above {ι : Type*} {x : ι → ℝ} (hxs : Summable fun i => x i ^ 2)
    {d : ℝ} (hd : 0 < d) : {c : ℝ | d ≤ c ∧ 0 < mult x c}.Finite := by
  refine ((finite_ge hxs hd).image x).subset fun c hc => ?_
  obtain ⟨i, hi⟩ := exists_eq_of_mult_pos hc.2
  exact ⟨i, by simp only [Set.mem_ofPred_eq]; rw [hi]; exact hc.1, hi⟩

/-- A nonempty set of reals that is finite above each of its elements has a greatest
element. Applied to the set of values where two multiplicity functions disagree. -/
theorem exists_max {D : Set ℝ} (hne : D.Nonempty)
    (hfin : ∀ d ∈ D, {c ∈ D | d ≤ c}.Finite) : ∃ c₀ ∈ D, ∀ c ∈ D, c ≤ c₀ := by
  obtain ⟨d, hd⟩ := hne
  have hF := hfin d hd
  have hFne : {c ∈ D | d ≤ c}.Nonempty := ⟨d, hd, le_refl d⟩
  obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image {c ∈ D | d ≤ c} id hF hFne
  refine ⟨c₀, hc₀.1, fun c hcD => ?_⟩
  rcases le_or_gt d c with hdc | hdc
  · exact hmax c ⟨hcD, hdc⟩
  · exact le_trans hdc.le hc₀.2

/-- For a value above the threshold, the restricted fibre is the full fibre. -/
def fiberAboveEquiv {ι : Type*} (x : ι → ℝ) {t c : ℝ} (hc : t < c) :
    {p : {i // t < x i} // x p.1 = c} ≃ {i // x i = c} where
  toFun p := ⟨p.1.1, p.2⟩
  invFun i := ⟨⟨i.1, by rw [i.2]; exact hc⟩, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_equiv_above {ι κ : Type*} {x : ι → ℝ} {y : κ → ℝ} {t : ℝ}
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ k, 0 < y k)
    (hfx : ∀ c, 0 < c → {i | x i = c}.Finite) (hfy : ∀ c, 0 < c → {k | y k = c}.Finite)
    (h : ∀ c, t < c → mult x c = mult y c) :
    ∃ e : {i // t < x i} ≃ {k // t < y k}, ∀ p : {i // t < x i}, x p.1 = y (e p).1 := by
  have hmult : ∀ c, 0 < c → mult (fun p : {i // t < x i} => x p.1) c
      = mult (fun q : {k // t < y k} => y q.1) c := by
    intro c hc
    rcases lt_or_ge t c with htc | htc
    · rw [mult, mult, Nat.card_congr (fiberAboveEquiv x htc),
        Nat.card_congr (fiberAboveEquiv y htc)]
      exact h c htc
    · have e1 : IsEmpty {p : {i // t < x i} // x p.1 = c} :=
        ⟨fun p => absurd (p.2 ▸ p.1.2) (not_lt.mpr htc)⟩
      have e2 : IsEmpty {q : {k // t < y k} // y q.1 = c} :=
        ⟨fun q => absurd (q.2 ▸ q.1.2) (not_lt.mpr htc)⟩
      simp [mult, Nat.card_of_isEmpty]
  refine exists_equiv_of_mult_eq (x := fun p : {i // t < x i} => x p.1)
    (y := fun q : {k // t < y k} => y q.1)
    (fun p => hx0 p.1) (fun q => hy0 q.1) (fun c hc => ?_) (fun c hc => ?_) hmult
  · exact (hfx c hc).preimage Subtype.val_injective.injOn
  · exact (hfy c hc).preimage Subtype.val_injective.injOn

/-- In the tail (values at most `c₀`), the value `c₀` is attained exactly where the family
rescaled by `c₀` attains `1`. -/
def tailFiberEquiv {ι : Type*} (x : ι → ℝ) {c₀ : ℝ} (hc₀ : c₀ ≠ 0) :
    {p : (({i | c₀ < x i})ᶜ : Set ι) // x p.1 / c₀ = 1} ≃ {i // x i = c₀} where
  toFun p := ⟨p.1.1, (div_eq_one_iff_eq hc₀).mp p.2⟩
  invFun i := ⟨⟨i.1, by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, i.2]
      exact le_rfl⟩,
    (div_eq_one_iff_eq hc₀).mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The analysis step -/

/-- Families in `(0, 1]` with the same power sums from `2` on attain every
value with the same multiplicity.

The proof is a minimal counterexample rather than an induction. Local finiteness makes the set of
values where the multiplicities differ have a *least* element `c₀`. The multiplicities agree
below `c₀`, so the finite "head" sums agree and can be subtracted, leaving the tails equal. For
the tails, `c₀ ^ (-n) * ∑ᵢ xᵢ ⁿ → mult x c₀` as `n → ∞` by dominated convergence, since the
strictly smaller values are crushed. Hence `mult x c₀ = mult y c₀`, a contradiction. -/
theorem mult_eq_mult {ι κ : Type*} {x : ι → ℝ} {y : κ → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i ≤ 1) (hy0 : ∀ k, 0 < y k) (hy1 : ∀ k, y k ≤ 1)
    (hxs : Summable fun i => x i ^ 2) (hys : Summable fun k => y k ^ 2)
    (h : ∀ n, 2 ≤ n → ∑' i, x i ^ n = ∑' k, y k ^ n) :
    ∀ c, 0 < c → mult x c = mult y c := by
  -- Summability at every exponent `≥ 2`, since the values are at most `1`.
  have hsx : ∀ n, 2 ≤ n → Summable fun i => x i ^ n := fun n hn =>
    hxs.of_nonneg_of_le (fun i => pow_nonneg (hx0 i).le n)
      (fun i => pow_le_pow_of_le_one (hx0 i).le (hx1 i) hn)
  have hsy : ∀ n, 2 ≤ n → Summable fun k => y k ^ n := fun n hn =>
    hys.of_nonneg_of_le (fun k => pow_nonneg (hy0 k).le n)
      (fun k => pow_le_pow_of_le_one (hy0 k).le (hy1 k) hn)
  have hfx : ∀ c, 0 < c → {i | x i = c}.Finite := fun c hc => finite_fiber hxs hc
  have hfy : ∀ c, 0 < c → {k | y k = c}.Finite := fun c hc => finite_fiber hys hc
  -- Suppose not, and take the greatest value where the multiplicities disagree.
  by_contra hcon
  push Not at hcon
  obtain ⟨cbad, hcbad, hnebad⟩ := hcon
  have hDfin : ∀ d ∈ {c : ℝ | 0 < c ∧ mult x c ≠ mult y c},
      {c' ∈ {c : ℝ | 0 < c ∧ mult x c ≠ mult y c} | d ≤ c'}.Finite := by
    intro d hd
    refine ((finite_values_above hxs hd.1).union (finite_values_above hys hd.1)).subset ?_
    intro c' hc'
    obtain ⟨⟨_, hne⟩, hdc'⟩ := hc'
    rcases Nat.eq_zero_or_pos (mult x c') with h0 | hp
    · refine Or.inr ⟨hdc', ?_⟩
      rcases Nat.eq_zero_or_pos (mult y c') with h0' | hp'
      · exact absurd (h0.trans h0'.symm) hne
      · exact hp'
    · exact Or.inl ⟨hdc', hp⟩
  obtain ⟨c₀, hc₀D, hc₀max⟩ :=
    exists_max (D := {c : ℝ | 0 < c ∧ mult x c ≠ mult y c}) ⟨cbad, hcbad, hnebad⟩ hDfin
  obtain ⟨hc₀pos, hc₀ne⟩ := hc₀D
  -- Above `c₀` the multiplicities agree, so the heads match up bijectively.
  have hagree : ∀ c', c₀ < c' → mult x c' = mult y c' := by
    intro c' hlt
    by_contra hne
    have := hc₀max c' ⟨lt_trans hc₀pos hlt, hne⟩
    linarith
  obtain ⟨e, he⟩ := exists_equiv_above (t := c₀) hx0 hy0 hfx hfy hagree
  have hheads : ∀ n : ℕ, ∑' p : (({i | c₀ < x i}) : Set ι), x p.1 ^ n
      = ∑' q : (({k | c₀ < y k}) : Set κ), y q.1 ^ n := fun n =>
    (tsum_congr fun p : {i // c₀ < x i} => by rw [he p]).trans (e.tsum_eq _)
  -- Subtracting the heads from the totals leaves the tails equal.
  have htails : ∀ n : ℕ, 2 ≤ n → ∑' p : ((({i | c₀ < x i})ᶜ) : Set ι), x p.1 ^ n
      = ∑' q : ((({k | c₀ < y k})ᶜ) : Set κ), y q.1 ^ n := by
    intro n hn
    have hxsplit := (hsx n hn).tsum_subtype_add_tsum_subtype_compl {i | c₀ < x i}
    have hysplit := (hsy n hn).tsum_subtype_add_tsum_subtype_compl {k | c₀ < y k}
    have := h n hn
    rw [← hxsplit, ← hysplit, hheads n] at this
    linarith
  -- Rescale the tails by `c₀`: values land in `(0, 1]`, with `1` exactly on the `c₀`-fibre.
  have hzx0 : ∀ p : ((({i | c₀ < x i})ᶜ) : Set ι), 0 < x p.1 / c₀ :=
    fun p => div_pos (hx0 _) hc₀pos
  have hzy0 : ∀ q : ((({k | c₀ < y k})ᶜ) : Set κ), 0 < y q.1 / c₀ :=
    fun q => div_pos (hy0 _) hc₀pos
  have hzx1 : ∀ p : ((({i | c₀ < x i})ᶜ) : Set ι), x p.1 / c₀ ≤ 1 := by
    intro p
    have hp : ¬ c₀ < x p.1 := p.2
    exact (div_le_one hc₀pos).mpr (not_lt.mp hp)
  have hzy1 : ∀ q : ((({k | c₀ < y k})ᶜ) : Set κ), y q.1 / c₀ ≤ 1 := by
    intro q
    have hq : ¬ c₀ < y q.1 := q.2
    exact (div_le_one hc₀pos).mpr (not_lt.mp hq)
  have hzxs : Summable fun p : ((({i | c₀ < x i})ᶜ) : Set ι) => (x p.1 / c₀) ^ 2 := by
    exact ((hxs.subtype _).div_const (c₀ ^ 2)).congr fun p => (div_pow (x p.1) c₀ 2).symm
  have hzys : Summable fun q : ((({k | c₀ < y k})ᶜ) : Set κ) => (y q.1 / c₀) ^ 2 := by
    exact ((hys.subtype _).div_const (c₀ ^ 2)).congr fun q => (div_pow (y q.1) c₀ 2).symm
  -- The rescaled tails have equal power sums, so their limits agree.
  have hzeq : ∀ n : ℕ, 2 ≤ n →
      ∑' p : ((({i | c₀ < x i})ᶜ) : Set ι), (x p.1 / c₀) ^ n
        = ∑' q : ((({k | c₀ < y k})ᶜ) : Set κ), (y q.1 / c₀) ^ n := by
    intro n hn
    rw [tsum_congr fun p : ((({i | c₀ < x i})ᶜ) : Set ι) => div_pow (x p.1) c₀ n,
      tsum_div_const,
      tsum_congr fun q : ((({k | c₀ < y k})ᶜ) : Set κ) => div_pow (y q.1) c₀ n,
      tsum_div_const, htails n hn]
  have hlimx := tendsto_tsum_pow hzx0 hzx1 hzxs
  have hlimy := tendsto_tsum_pow hzy0 hzy1 hzys
  have heq : (fun n : ℕ => ∑' p : ((({i | c₀ < x i})ᶜ) : Set ι), (x p.1 / c₀) ^ n)
      =ᶠ[atTop] fun n => ∑' q : ((({k | c₀ < y k})ᶜ) : Set κ), (y q.1 / c₀) ^ n := by
    filter_upwards [eventually_ge_atTop 2] with n hn using hzeq n hn
  have hcards := tendsto_nhds_unique (Filter.Tendsto.congr' heq hlimx) hlimy
  -- Read the limits back as multiplicities at `c₀`.
  have hcx : Nat.card {p : ((({i | c₀ < x i})ᶜ) : Set ι) // x p.1 / c₀ = 1} = mult x c₀ :=
    Nat.card_congr (tailFiberEquiv x hc₀pos.ne')
  have hcy : Nat.card {q : ((({k | c₀ < y k})ᶜ) : Set κ) // y q.1 / c₀ = 1} = mult y c₀ :=
    Nat.card_congr (tailFiberEquiv y hc₀pos.ne')
  rw [hcx, hcy] at hcards
  exact hc₀ne (by exact_mod_cast hcards)



/-! ## The theorem used downstream -/

/-- **Uniqueness for power sums.** Two families in `(0, 1]` whose power sums agree from exponent
`2` onwards are the same family up to a relabelling of the index set. -/
theorem exists_equiv_of_tsum_pow_eq {ι κ : Type*} {x : ι → ℝ} {y : κ → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i ≤ 1) (hy0 : ∀ k, 0 < y k) (hy1 : ∀ k, y k ≤ 1)
    (hxs : Summable fun i => x i ^ 2) (hys : Summable fun k => y k ^ 2)
    (h : ∀ n, 2 ≤ n → ∑' i, x i ^ n = ∑' k, y k ^ n) :
    ∃ e : ι ≃ κ, ∀ i, x i = y (e i) :=
  exists_equiv_of_mult_eq hx0 hy0 (fun _ hc => finite_fiber hxs hc)
    (fun _ hc => finite_fiber hys hc) (mult_eq_mult hx0 hx1 hy0 hy1 hxs hys h)

/-! ## Bridge from the `rpow` formulation -/

/-- At integer arguments a negative real power is an ordinary power of the inverse. This is what
lets the ζ-hypothesis, stated with `Real.rpow`, feed the power-sum machinery above. -/
lemma rpow_neg_natCast_eq_inv_pow {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ (-(n : ℝ)) = t⁻¹ ^ n := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]

end ZetaRigidity

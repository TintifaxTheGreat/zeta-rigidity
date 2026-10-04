/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Model
import ZetaRigidity.DirichletUniqueness

/-!
# The order the construction determines on its own

Before any valuation is chosen, the abstract primes carry only their indexing. This file
determines exactly how much of the ordering of the formal products that already fixes.

Write `tailDegree m j` for the number of prime factors of `m` of index at least `j`, counted
with multiplicity, and say `m` is universally below `n` when `v.extend m ≤ v.extend n` holds for
every valuation `v`. The two notions agree:

`universallyLE_iff : UniversallyLE m n ↔ ∀ j, tailDegree m j ≤ tailDegree n j`

## Main results

* `universallyLE_iff`: the characterisation above.
* `universallyLE_of_dvd`: divisibility is a special case, and `not_dvd_atom_zero_atom_one` shows
  the containment is strict.
* `not_universallyLE_sq`, `not_universallyLE_mul`: the order is genuinely partial. In particular
  `p₀ · p₁` and `p₂` are incomparable, so the construction does not decide which is larger.

## What this says

The resulting order is strictly between divisibility and a total order. It refines `degree`
(take `j = 0`) and it is coarser than any particular valuation's ordering. Together with
`autEquivPerm` (`ZetaRigidity/Automorphisms.lean`) it brackets what the construction knows
before the ζ-condition is imposed: without the indexing of the atoms, nothing at all, since
every permutation of the primes is a symmetry; with it, exactly `tailDegree` domination. A total
order has to come from outside.
-/

namespace ZetaRigidity

/-! ## Tail degrees -/

/-- The number of prime factors of `m` of index at least `j`, counted with multiplicity. -/
noncomputable def tailDegree (m : FormalProd) (j : ℕ) : ℕ :=
  (Multiplicative.toAdd m).sum fun i k => if j ≤ i then k else 0

@[simp] lemma tailDegree_one (j : ℕ) : tailDegree 1 j = 0 := rfl

@[simp] lemma tailDegree_mul (m n : FormalProd) (j : ℕ) :
    tailDegree (m * n) j = tailDegree m j + tailDegree n j :=
  Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by split_ifs <;> simp)

@[simp] lemma tailDegree_atom (i j : ℕ) : tailDegree (atom i) j = if j ≤ i then 1 else 0 := by
  change (Finsupp.single i 1).sum (fun a k => if j ≤ a then k else 0) = _
  rw [Finsupp.sum_single_index]
  simp

@[simp] lemma tailDegree_pow (m : FormalProd) (k j : ℕ) :
    tailDegree (m ^ k) j = k * tailDegree m j := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, tailDegree_mul, ih]; ring

/-- At `j = 0` the tail degree is the total number of prime factors, so the order below refines
`degree`. -/
@[simp] lemma tailDegree_zero_eq_degree (m : FormalProd) : tailDegree m 0 = degree m :=
  Finset.sum_congr rfl fun i _ => by simp

/-- Peeling one index off a tail. Stated additively to avoid truncated subtraction; it says the
tail degrees determine the exponents, hence determine the formal product. -/
lemma tailDegree_succ (m : FormalProd) (j : ℕ) :
    tailDegree m j = expo m j + tailDegree m (j + 1) := by
  have hsplit : ∀ i : ℕ, (if j ≤ i then (Multiplicative.toAdd m) i else 0)
      = (if i = j then (Multiplicative.toAdd m) i else 0)
        + (if j + 1 ≤ i then (Multiplicative.toAdd m) i else 0) := by
    intro i; split_ifs <;> omega
  change ∑ i ∈ (Multiplicative.toAdd m).support, _ = _
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Multiplicative.toAdd m).support j]
  congr 1
  by_cases hj : j ∈ (Multiplicative.toAdd m).support
  · simp only [hj, reduceIte]
    rfl
  · simp only [hj, reduceIte]
    exact (Finsupp.notMem_support_iff.mp hj).symm

/-- Beyond the largest index occurring in `m`, the tail degree vanishes. -/
lemma tailDegree_eq_zero_of_forall_lt {m : FormalProd} {j : ℕ}
    (h : ∀ i ∈ (Multiplicative.toAdd m).support, i < j) : tailDegree m j = 0 :=
  Finset.sum_eq_zero fun i hi => by
    have := h i hi
    simp only [Nat.not_le.mpr this, reduceIte]

/-- The tail degrees form a complete invariant: equal tails means equal formal products. -/
lemma ext_tailDegree {m n : FormalProd} (h : ∀ j, tailDegree m j = tailDegree n j) : m = n := by
  refine ext_expo fun j => ?_
  have hm := tailDegree_succ m j
  have hn := tailDegree_succ n j
  rw [h j, h (j + 1)] at hm
  omega

/-! ## The universal order -/

/-- `m` lies below `n` in every valuation. -/
def UniversallyLE (m n : FormalProd) : Prop := ∀ v : Valuation, v.extend m ≤ v.extend n

/-! ### Tail domination is sufficient

The proof peels the largest atom off `m` and matches it with an atom of `n` of index at least as
large, which the tail condition supplies. This is Hall's marriage argument specialised to the
present situation.
-/

private lemma universallyLE_aux : ∀ (d : ℕ) (m n : FormalProd), degree m = d →
    (∀ j, tailDegree m j ≤ tailDegree n j) → ∀ v : Valuation, v.extend m ≤ v.extend n := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m n hdeg htail v
    rcases eq_or_ne m 1 with rfl | hm
    · simpa using v.one_le_extend n
    -- The largest index occurring in `m`.
    have hne : (Multiplicative.toAdd m).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr fun h => hm (Multiplicative.toAdd.injective h)
    set a := (Multiplicative.toAdd m).support.max' hne with ha
    have hamem : a ∈ (Multiplicative.toAdd m).support := Finset.max'_mem _ hne
    have hale : ∀ i ∈ (Multiplicative.toAdd m).support, i ≤ a := fun i hi =>
      Finset.le_max' _ i hi
    have hapos : 0 < expo m a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hamem)
    -- So `m` has a factor of index `≥ a`, hence so does `n`.
    have hma : 1 ≤ tailDegree m a := by
      rw [tailDegree_succ]
      have : tailDegree m (a + 1) = 0 :=
        tailDegree_eq_zero_of_forall_lt fun i hi => by have := hale i hi; omega
      omega
    have hna : 1 ≤ tailDegree n a := le_trans hma (htail a)
    obtain ⟨b, hbmem, hab⟩ : ∃ b ∈ (Multiplicative.toAdd n).support, a ≤ b := by
      by_contra hcon
      push Not at hcon
      exact absurd (tailDegree_eq_zero_of_forall_lt fun i hi => by
        have := hcon i hi; omega) (by omega)
    have hbpos : 0 < expo n b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hbmem)
    obtain ⟨m', hm'⟩ := exists_eq_atom_mul hapos
    obtain ⟨n', hn'⟩ := exists_eq_atom_mul hbpos
    -- The tail condition passes to the smaller pair.
    have htail' : ∀ j, tailDegree m' j ≤ tailDegree n' j := by
      intro j
      have hm2 := htail j
      rw [hm', hn', tailDegree_mul, tailDegree_mul, tailDegree_atom, tailDegree_atom] at hm2
      by_cases hja : j ≤ a
      · have e1 : (if j ≤ a then 1 else 0) = 1 := by simp [hja]
        have e2 : (if j ≤ b then 1 else 0) = 1 := by simp [le_trans hja hab]
        rw [e1, e2] at hm2
        omega
      · have hzero : tailDegree m' j = 0 := by
          have hmj : tailDegree m j = 0 :=
            tailDegree_eq_zero_of_forall_lt fun i hi => by have := hale i hi; omega
          rw [hm', tailDegree_mul] at hmj
          omega
        omega
    -- Degree drops, so the induction hypothesis applies.
    have hdeg' : degree m' < d := by
      rw [← hdeg, hm', degree_mul, degree_atom]
      omega
    have hrec := ih (degree m') hdeg' m' n' rfl htail' v
    rw [hm', hn', map_mul, map_mul, v.extend_atom, v.extend_atom]
    exact mul_le_mul (v.strictMono.monotone hab) hrec (v.extend_pos m').le (v.pos b).le

/-- Tail domination is sufficient: if `m` has at most as many prime factors of index `≥ j` as
`n` does, for every `j`, then `m` is below `n` in every valuation. -/
theorem universallyLE_of_tailDegree {m n : FormalProd}
    (h : ∀ j, tailDegree m j ≤ tailDegree n j) : UniversallyLE m n :=
  universallyLE_aux (degree m) m n rfl h

/-! ### Tail domination is necessary

If the tail condition fails at some index `k`, a valuation separating `m` from `n` can be
written down. Taking logarithms, a valuation is exactly a strictly increasing sequence of
positive reals, so it suffices to choose one giving every prime of index `≥ k` a large extra
weight `T`. The sum then differs by `T` times the gap in tail degrees, plus a bounded term.
-/

/-- The total index weight of a formal product, the bounded term in the estimate below. -/
private noncomputable def weight (m : FormalProd) : ℕ :=
  (Multiplicative.toAdd m).sum fun i k => k * (i + 1)

/-- The valuation giving index `i` the logarithmic value `i + 1`, with an extra `T` once `i`
reaches `k`. Used below to separate formal products whose tail degrees differ at `k`, and useful
on its own as a source of valuations that order the primes very unevenly. -/
noncomputable def stepVal (k : ℕ) (T : ℝ) (hT : 0 ≤ T) : Valuation where
  toFun i := Real.exp ((i + 1) + if k ≤ i then T else 0)
  one_lt' i := by
    refine Real.one_lt_exp_iff.mpr ?_
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    split_ifs <;> linarith
  strictMono' a b hab := by
    refine Real.exp_lt_exp.mpr ?_
    have hcast : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hstep : (if k ≤ a then T else 0) ≤ (if k ≤ b then T else 0) := by
      split_ifs with h1 h2 h2
      · exact le_rfl
      · omega
      · exact hT
      · exact le_rfl
    linarith

@[simp] lemma stepVal_apply (k : ℕ) (T : ℝ) (hT : 0 ≤ T) (i : ℕ) :
    stepVal k T hT i = Real.exp ((i + 1) + if k ≤ i then T else 0) := rfl

/-- The logarithm of a `stepVal` magnitude splits into a bounded term and `T` times the tail
degree at `k`. This is what makes `T` able to swamp everything else. -/
lemma log_stepVal (k : ℕ) (T : ℝ) (hT : 0 ≤ T) (m : FormalProd) :
    Real.log ((stepVal k T hT).extend m) = (weight m : ℝ) + T * (tailDegree m k : ℝ) := by
  rw [Valuation.log_extend]
  change ∑ i ∈ (Multiplicative.toAdd m).support, _ = _
  unfold weight tailDegree
  change _ = ((∑ i ∈ (Multiplicative.toAdd m).support, _ : ℕ) : ℝ)
      + T * ((∑ i ∈ (Multiplicative.toAdd m).support, _ : ℕ) : ℝ)
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ((Multiplicative.toAdd m) i : ℝ) * Real.log (Real.exp _) = _
  rw [Real.log_exp]
  split_ifs <;> ring

/-- Tail domination is necessary: if the counts fail to dominate at some index, `stepVal` at
that index separates the two formal products. -/
theorem tailDegree_of_universallyLE {m n : FormalProd} (h : UniversallyLE m n) (j : ℕ) :
    tailDegree m j ≤ tailDegree n j := by
  by_contra hcon
  push Not at hcon
  -- Choose the extra weight large enough to swamp the bounded term.
  set T : ℝ := (weight m : ℝ) + (weight n : ℝ) + 1 with hTdef
  have hT : 0 ≤ T := by positivity
  have hle := h (stepVal j T hT)
  have hlog := Real.log_le_log (Valuation.extend_pos _ m) hle
  rw [log_stepVal, log_stepVal] at hlog
  -- The gap in tail degrees is at least one.
  have hgap : (tailDegree n j : ℝ) + 1 ≤ (tailDegree m j : ℝ) := by
    have : tailDegree n j + 1 ≤ tailDegree m j := hcon
    exact_mod_cast this
  have hwm : (0 : ℝ) ≤ (weight m : ℝ) := Nat.cast_nonneg _
  have hwn : (0 : ℝ) ≤ (weight n : ℝ) := Nat.cast_nonneg _
  have htn : (0 : ℝ) ≤ (tailDegree n j : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog, hgap, hwm, hwn, htn]

/-- The order determined by the construction alone. -/
theorem universallyLE_iff {m n : FormalProd} :
    UniversallyLE m n ↔ ∀ j, tailDegree m j ≤ tailDegree n j :=
  ⟨fun h j => tailDegree_of_universallyLE h j, universallyLE_of_tailDegree⟩

/-! ## The order, and what it does not decide -/

/-- `UniversallyLE` is antisymmetric, so it is a genuine partial order; reflexivity and
transitivity are immediate from the definition.

It is deliberately left as a predicate rather than registered as a `PartialOrder` instance:
`FormalProd` already carries a `≤` inherited pointwise from `Finsupp`, and a second instance
would clash with it. -/
lemma universallyLE_antisymm {m n : FormalProd} (h₁ : UniversallyLE m n)
    (h₂ : UniversallyLE n m) : m = n :=
  ext_tailDegree fun j =>
    le_antisymm (universallyLE_iff.mp h₁ j) (universallyLE_iff.mp h₂ j)

/-- Divisibility is a special case. -/
theorem universallyLE_of_dvd {m n : FormalProd} (h : m ∣ n) : UniversallyLE m n := by
  obtain ⟨c, rfl⟩ := h
  exact fun v => by
    rw [map_mul]
    exact le_mul_of_one_le_right (v.extend_pos m).le (v.one_le_extend c)

/-- The order is strictly coarser than divisibility: the first prime is below the second in
every valuation, but does not divide it. -/
theorem universallyLE_atom_succ (i : ℕ) : UniversallyLE (atom i) (atom (i + 1)) := by
  refine universallyLE_of_tailDegree fun j => ?_
  rw [tailDegree_atom, tailDegree_atom]
  split_ifs <;> omega

/-- The square of the first prime and the second prime are not comparable. This is the smallest
pair the construction fails to order. -/
theorem not_universallyLE_sq :
    ¬ UniversallyLE (atom 0 ^ 2) (atom 1) ∧ ¬ UniversallyLE (atom 1) (atom 0 ^ 2) := by
  constructor
  · intro h
    have := universallyLE_iff.mp h 0
    simp [pow_two] at this
  · intro h
    have := universallyLE_iff.mp h 1
    simp [pow_two] at this

/-- The construction does not decide whether `p₀ · p₁` exceeds `p₂`. Both orderings occur, for
different valuations; see `ZetaRigidity/Examples.lean` for the two witnesses. -/
theorem not_universallyLE_mul :
    ¬ UniversallyLE (atom 0 * atom 1) (atom 2) ∧ ¬ UniversallyLE (atom 2) (atom 0 * atom 1) := by
  constructor
  · intro h
    have := universallyLE_iff.mp h 0
    simp at this
  · intro h
    have := universallyLE_iff.mp h 2
    simp at this

/-! ## Local finiteness does not determine the order

One might hope that strengthening the hypothesis would close the gap: ask for a *total* order
with strictly monotone multiplication, increasing atoms, and order type ω, meaning finitely many
elements below any bound. That is still not enough.

The witness is the system whose atoms are the primes from the second on, `3, 5, 7, 11, …`. Its
values are `1, 3, 5, 7, 9, 11, …`, so it is locally finite, and multiplication is monotone
because it is ordinary multiplication of reals. But it puts `p₀² = 9` above `p₂ = 7`, while the
ordinary primes put `p₀² = 4` below `p₂ = 5`. An isomorphism of ordered monoids must carry atoms
to atoms in order, so the two orders are not isomorphic.

What separates `ℤ_{>0}` is that its values have no gaps, and that is exactly the bijection
condition `isZetaNormalized_of_equiv` in `ZetaRigidity/Model.lean`, already equivalent to the
ζ-condition.
-/

/-- A valuation summable at `s = 2` has finitely many formal products below any bound, so the
order it induces has type ω. -/
lemma finite_below {v : Valuation}
    (hv : Summable fun m : FormalProd => v.extend m ^ (-2 : ℝ)) (x : ℝ) :
    {m : FormalProd | v.extend m ≤ x}.Finite := by
  rcases le_or_gt x 0 with hx | hx
  · refine Set.Finite.subset (Set.finite_empty) fun m hm => ?_
    exact absurd (le_trans hm hx) (not_le.mpr (v.extend_pos m))
  · refine Set.Finite.subset (finite_above hv (Real.rpow_pos_of_pos hx (-2))) fun m hm => ?_
    have hle : v.extend m ≤ x := hm
    exact Real.rpow_le_rpow_of_nonpos (v.extend_pos m) hle (by norm_num)

/-- The generalized prime system whose atoms are the primes from the second on. -/
noncomputable def shiftedVal : Valuation where
  toFun i := (Nat.nth Nat.Prime (i + 1) : ℝ)
  one_lt' i := by exact_mod_cast (nth_prime_prime (i + 1)).one_lt
  strictMono' _ _ h :=
    Nat.cast_lt.mpr (Nat.nth_strictMono primes_infinite (by omega))

@[simp] lemma shiftedVal_apply (i : ℕ) : shiftedVal i = (Nat.nth Nat.Prime (i + 1) : ℝ) := rfl

lemma primeVal_le_shiftedVal (i : ℕ) : primeVal i ≤ shiftedVal i := by
  simp only [shiftedVal_apply]
  have : primeVal i = (Nat.nth Nat.Prime i : ℝ) := rfl
  rw [this]
  exact_mod_cast (Nat.nth_strictMono primes_infinite (Nat.lt_succ_self i)).le

/-- Summability for the shifted system, by comparison with the ordinary primes rather than from
scratch. -/
lemma shiftedVal_summable :
    Summable fun m : FormalProd => shiftedVal.extend m ^ (-2 : ℝ) := by
  refine Summable.of_nonneg_of_le (fun m => Real.rpow_nonneg (shiftedVal.extend_pos m).le _)
    (fun m => ?_) primeVal_isZetaNormalized.summable
  exact Real.rpow_le_rpow_of_nonpos (primeVal.extend_pos m)
    (Valuation.extend_mono primeVal_le_shiftedVal m) (by norm_num)

/-- Local finiteness, monotone multiplication and increasing atoms do not force the ordinary
primes: `shiftedVal` satisfies all three and orders `atom 2` against `atom 0 ^ 2` the opposite
way round. -/
theorem exists_locallyFinite_order_ne_primes :
    ∃ w : Valuation,
      (∀ x : ℝ, {m : FormalProd | w.extend m ≤ x}.Finite) ∧
      ∃ m n : FormalProd, w.extend m < w.extend n ∧ primeVal.extend n < primeVal.extend m := by
  refine ⟨shiftedVal, fun x => finite_below shiftedVal_summable x, atom 2, atom 0 ^ 2, ?_, ?_⟩
  · rw [Valuation.extend_atom, map_pow, Valuation.extend_atom, shiftedVal_apply,
      shiftedVal_apply]
    rw [show Nat.nth Nat.Prime 3 = 7 from Nat.nth_prime_three_eq_seven,
      show Nat.nth Nat.Prime 1 = 3 from Nat.nth_prime_one_eq_three]
    norm_num
  · rw [Valuation.extend_atom, map_pow, Valuation.extend_atom]
    simp only [primeVal, Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
    norm_num

end ZetaRigidity

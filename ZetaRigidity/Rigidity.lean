/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Valuation
import ZetaRigidity.DirichletUniqueness

/-!
# ζ-rigidity

The main theorem: if the Dirichlet series of a valuation agrees with the Riemann zeta function
at the integers `2, 3, 4, …`, then the valuation is forced -- the `i`-th abstract prime has
value the `i`-th ordinary prime (`eq_nth_prime_of_isZetaNormalized`), and the formal products
are carried bijectively and multiplicatively onto the positive integers.

## What the hypothesis really says

`IsZetaNormalized v` holds *iff* `v.extend` is a multiplicative bijection onto `ℤ_{>0}`. The
hypothesis is therefore equivalent to the conclusion; the content is that a Dirichlet series
determines its exponents, not that ζ mysteriously detects primes. What ζ supplies is the
multiset `{1, 2, 3, …}`.

Note also that agreement is only required at integer arguments, so the theorem says: the values
`ζ(2), ζ(3), ζ(4), …` already determine the primes.
-/

namespace ZetaRigidity

open Filter

/-! ## Uniqueness of strictly monotone enumerations -/

private theorem le_of_strictMono_of_range_subset {u w : ℕ → ℕ} (hu : StrictMono u)
    (hw : StrictMono w) (h : Set.range w ⊆ Set.range u) : ∀ n, u n ≤ w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, hm⟩ := h ⟨n, rfl⟩
    rcases lt_or_ge m n with hmn | hmn
    · exfalso
      have h1 : u m ≤ w m := ih m hmn
      have h2 : w m < w n := hw hmn
      omega
    · exact hm ▸ hu.monotone hmn

/-- Two strictly monotone sequences of naturals with the same range are equal: a set has only
one increasing enumeration. -/
theorem strictMono_eq_of_range_eq {u w : ℕ → ℕ} (hu : StrictMono u) (hw : StrictMono w)
    (h : Set.range u = Set.range w) : u = w :=
  funext fun n => le_antisymm
    (le_of_strictMono_of_range_subset hu hw h.ge n)
    (le_of_strictMono_of_range_subset hw hu h.le n)

/-! ## The ζ-normalization hypothesis -/

lemma summable_natSucc_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s) := by
  have h : Summable fun n : ℕ => (((n : ℝ)) ^ s)⁻¹ := Real.summable_nat_rpow_inv.mpr hs
  have h2 : Summable fun n : ℕ => ((n : ℝ)) ^ (-s) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using h
  refine ((summable_nat_add_iff 1).mpr h2).congr fun n => ?_
  push_cast
  ring_nf

/-- The normalization condition: the Dirichlet series of `v` over all formal products converges,
and its values at the integers `2, 3, 4, …` are those of `ζ`. -/
structure IsZetaNormalized (v : Valuation) : Prop where
  /-- Convergence, needed at one point only. -/
  summable : Summable fun m : FormalProd => v.extend m ^ (-2 : ℝ)
  /-- Agreement with `ζ` at every integer `≥ 2`. -/
  agrees : ∀ k : ℕ, 2 ≤ k →
    ∑' m : FormalProd, v.extend m ^ (-(k : ℝ)) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(k : ℝ))

variable {v : Valuation}

/-- **Step 1.** The valuation enumerates the positive integers: there is a bijection from formal
products to `ℕ` under which the magnitude of `m` is `e m + 1`.

The ζ-hypothesis is stated with `Real.rpow`, while the uniqueness engine works with ordinary
powers of the inverses; `rpow_neg_natCast_eq_inv_pow` converts between them. -/
theorem exists_equiv_nat (h : IsZetaNormalized v) :
    ∃ e : FormalProd ≃ ℕ, ∀ m, v.extend m = (e m : ℝ) + 1 := by
  -- Positivity facts for the two families of values.
  have hVpos : ∀ m : FormalProd, 0 < v.extend m := v.extend_pos
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  -- Rewrite both sides of the hypothesis in terms of `(·)⁻¹ ^ n`.
  have hconvV : ∀ (n : ℕ) (m : FormalProd),
      v.extend m ^ (-(n : ℝ)) = (v.extend m)⁻¹ ^ n :=
    fun n m => rpow_neg_natCast_eq_inv_pow (hVpos m) n
  have hconvN : ∀ (n : ℕ) (j : ℕ),
      ((j : ℝ) + 1) ^ (-(n : ℝ)) = (((j : ℝ) + 1))⁻¹ ^ n :=
    fun n j => rpow_neg_natCast_eq_inv_pow (hNpos j) n
  -- Apply uniqueness of power sums to the inverted families.
  obtain ⟨e, he⟩ := exists_equiv_of_tsum_pow_eq
    (x := fun m : FormalProd => (v.extend m)⁻¹) (y := fun j : ℕ => ((j : ℝ) + 1)⁻¹)
    (fun m => inv_pos.mpr (hVpos m)) (fun m => inv_le_one_of_one_le₀ (v.one_le_extend m))
    (fun j => by positivity)
    (fun j => inv_le_one_of_one_le₀ (by simp))
    (by
      refine h.summable.congr fun m => ?_
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, hconvV 2 m])
    (by
      refine (summable_natSucc_rpow_neg one_lt_two).congr fun j => ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, hconvN 2 j])
    (by
      intro n hn
      have hag := h.agrees n hn
      rw [tsum_congr fun m => (hconvV n m).symm, tsum_congr fun j => (hconvN n j).symm]
      exact hag)
  -- Undo the inversion: equal inverses means equal values.
  exact ⟨e, fun m => inv_injective (he m)⟩

/-- **ζ-rigidity.** Under the normalization condition the `i`-th abstract prime has value the
`i`-th ordinary prime. Nothing about ordinary addition was assumed: the scale is supplied
entirely by the analytic identity. -/
theorem eq_nth_prime_of_isZetaNormalized (h : IsZetaNormalized v) (i : ℕ) :
    v i = (Nat.nth Nat.Prime i : ℝ) := by
  obtain ⟨e, he⟩ := exists_equiv_nat h
  -- `N m` is the ordinary positive integer represented by the formal product `m`.
  set N : FormalProd → ℕ := fun m => e m + 1 with hNdef
  have hN : ∀ m, v.extend m = (N m : ℝ) := by
    intro m; rw [he m, hNdef]; push_cast; ring
  have hNpos : ∀ m, 0 < N m := fun m => Nat.succ_pos _
  have hNinj : Function.Injective N := fun a b hab =>
    e.injective (by simp only [hNdef] at hab; omega)
  have hNsurj : ∀ n : ℕ, 0 < n → ∃ m, N m = n := by
    intro n hn
    exact ⟨e.symm (n - 1), by simp only [hNdef, Equiv.apply_symm_apply]; omega⟩
  have hNmul : ∀ a b, N (a * b) = N a * N b := by
    intro a b
    refine Nat.cast_injective (R := ℝ) ?_
    push_cast
    rw [← hN (a * b), ← hN a, ← hN b]
    exact map_mul v.extend a b
  have hN1 : N 1 = 1 := by
    refine Nat.cast_injective (R := ℝ) ?_
    push_cast
    rw [← hN 1]
    exact v.extend_one
  have hN_one_lt : ∀ m, m ≠ 1 → 1 < N m := by
    intro m hm
    have hlt := v.one_lt_extend hm
    rw [hN m] at hlt
    exact_mod_cast hlt
  -- Atoms are carried to ordinary primes, because a multiplicative bijection preserves atoms.
  have hprime : ∀ j, Nat.Prime (N (atom j)) := by
    intro j
    rw [← Nat.irreducible_iff_nat_prime]
    refine ⟨by rw [Nat.isUnit_iff]; exact (hN_one_lt _ (atom_ne_one j)).ne', fun a b hab => ?_⟩
    have hpos := hNpos (atom j)
    rw [hab] at hpos
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
    obtain ⟨m, hm⟩ := hNsurj a ha
    obtain ⟨n, hn⟩ := hNsurj b hb
    have : m * n = atom j := hNinj (by rw [hNmul, hm, hn, ← hab])
    rcases eq_one_or_eq_one_of_mul_eq_atom this with rfl | rfl
    · exact Or.inl (Nat.isUnit_iff.mpr (by rw [← hm, hN1]))
    · exact Or.inr (Nat.isUnit_iff.mpr (by rw [← hn, hN1]))
  -- `u` is the increasing enumeration of prime values.
  set u : ℕ → ℕ := fun j => N (atom j) with hudef
  have hu_mono : StrictMono u := by
    intro a b hab
    have h1 : v.extend (atom a) < v.extend (atom b) := by
      rw [v.extend_atom, v.extend_atom]; exact v.strictMono hab
    rw [hN, hN] at h1
    exact_mod_cast h1
  have hu_range : Set.range u = Set.ofPred Nat.Prime := by
    refine Set.eq_of_subset_of_subset ?_ fun p hp => ?_
    · rintro _ ⟨j, rfl⟩; exact hprime j
    · obtain ⟨m, hm⟩ := hNsurj p hp.pos
      have hm1 : m ≠ 1 := by rintro rfl; rw [hN1] at hm; exact hp.one_lt.ne' hm.symm
      obtain ⟨j, hj⟩ := exists_expo_pos hm1
      obtain ⟨m', hm'⟩ := exists_eq_atom_mul hj
      have hsplit : p = N (atom j) * N m' := by rw [← hm, hm', hNmul]
      have hdvd : N m' ∣ p := ⟨N (atom j), by rw [hsplit]; ring⟩
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · rw [h1, mul_one] at hsplit
        exact ⟨j, hsplit.symm⟩
      · exfalso
        rw [h1] at hsplit
        have hgt := hN_one_lt (atom j) (atom_ne_one j)
        have := hp.pos
        nlinarith
  -- Two increasing enumerations of the primes coincide.
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hu_eq : u = Nat.nth Nat.Prime :=
    strictMono_eq_of_range_eq hu_mono (Nat.nth_strictMono hinf)
      (by rw [hu_range, Nat.range_nth_of_infinite hinf])
  calc v i = v.extend (atom i) := (v.extend_atom i).symm
    _ = (u i : ℝ) := hN (atom i)
    _ = (Nat.nth Nat.Prime i : ℝ) := by rw [hu_eq]

end ZetaRigidity

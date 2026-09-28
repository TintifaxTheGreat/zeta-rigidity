/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Rigidity

/-!
# The intended model, and non-vacuity

`eq_nth_prime_of_isZetaNormalized` would be true and worthless if nothing satisfied
`IsZetaNormalized`. This file rules that out by exhibiting the intended model -- the valuation
sending the `i`-th abstract prime to the `i`-th ordinary prime -- and **proving** it is
ζ-normalized (`primeVal_isZetaNormalized`).

The proof needs no Euler product. The ordinary integer represented by a formal product is
`val`, and unique factorisation says `val` is a bijection onto the positive integers; the
Dirichlet series identity is then just a reindexing of a `tsum` along that bijection.

Combined with `isZetaNormalized_of_equiv` this also establishes the claim made in
`ZetaRigidity/Rigidity.lean`: the ζ-hypothesis is *equivalent* to being a multiplicative
enumeration of the positive integers, not weaker than it.
-/

namespace ZetaRigidity

open Filter

/-! ## The converse of rigidity -/

/-- A multiplicative enumeration of the positive integers is ζ-normalized. With
`eq_nth_prime_of_isZetaNormalized`, this makes the hypothesis and the conclusion equivalent. -/
theorem isZetaNormalized_of_equiv {v : Valuation} (e : FormalProd ≃ ℕ)
    (he : ∀ m, v.extend m = (e m : ℝ) + 1) : IsZetaNormalized v where
  summable := by
    refine ((summable_natSucc_rpow_neg one_lt_two).comp_injective e.injective).congr fun m => ?_
    rw [he m]; rfl
  agrees k _ := by
    rw [tsum_congr fun m => by rw [he m]]
    exact e.tsum_eq fun n : ℕ => ((n : ℝ) + 1) ^ (-(k : ℝ))

/-! ## The intended valuation -/

lemma primes_infinite : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime

lemma nth_prime_prime (i : ℕ) : Nat.Prime (Nat.nth Nat.Prime i) :=
  Nat.nth_mem_of_infinite primes_infinite i

lemma nth_prime_injective : Function.Injective (Nat.nth Nat.Prime) :=
  (Nat.nth_strictMono primes_infinite).injective

/-- The intended valuation: the `i`-th abstract prime is sent to the `i`-th ordinary prime. -/
noncomputable def primeVal : Valuation where
  toFun i := (Nat.nth Nat.Prime i : ℝ)
  one_lt' i := by exact_mod_cast (nth_prime_prime i).one_lt
  strictMono' _ _ h := Nat.cast_lt.mpr (Nat.nth_strictMono primes_infinite h)

/-! ## The ordinary integer represented by a formal product -/

/-- Reindex a formal product's exponent vector from prime *indices* to the primes themselves. -/
noncomputable def toFactorization (m : FormalProd) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (Nat.nth Nat.Prime) (Multiplicative.toAdd m)

/-- The ordinary positive integer represented by a formal product. -/
noncomputable def val (m : FormalProd) : ℕ := (toFactorization m).prod (· ^ ·)

lemma toFactorization_support_prime {m : FormalProd} {p : ℕ}
    (hp : p ∈ (toFactorization m).support) : Nat.Prime p := by
  rw [toFactorization, Finsupp.mapDomain_support_of_injective nth_prime_injective] at hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact nth_prime_prime i

lemma toFactorization_injective : Function.Injective toFactorization := fun _ _ h =>
  Multiplicative.toAdd.injective (Finsupp.mapDomain_injective nth_prime_injective h)

/-- `val` really is the magnitude the intended valuation assigns. -/
lemma coe_val (m : FormalProd) : (val m : ℝ) = primeVal.extend m := by
  rw [val, toFactorization, Finsupp.prod_mapDomain_index_inj (h := (· ^ ·)) nth_prime_injective]
  change ((Finsupp.prod (Multiplicative.toAdd m) fun i k => Nat.nth Nat.Prime i ^ k : ℕ) : ℝ)
    = Finsupp.prod (Multiplicative.toAdd m) fun i k => (Nat.nth Nat.Prime i : ℝ) ^ k
  simp only [Finsupp.prod, Nat.cast_prod, Nat.cast_pow]

lemma val_pos (m : FormalProd) : 0 < val m := by
  have := primeVal.extend_pos m
  rw [← coe_val m] at this
  exact_mod_cast this

/-! ### Computation rules

`val` is noncomputable (`Finsupp.single`, `Finsupp.mapDomain` and `Nat.nth` all are), so `#eval`
is not available. These rules let `simp`/`norm_num` evaluate `val` on any concrete formal
product instead, which is how examples get checked. See `ZetaRigidity/Examples.lean`. -/

@[simp] lemma val_one : val (1 : FormalProd) = 1 := by
  have h : ((val (1 : FormalProd) : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := by
    push_cast
    rw [coe_val]
    exact primeVal.extend_one
  exact_mod_cast h

@[simp] lemma val_mul (m n : FormalProd) : val (m * n) = val m * val n := by
  have h : ((val (m * n) : ℕ) : ℝ) = ((val m * val n : ℕ) : ℝ) := by
    push_cast
    rw [coe_val m, coe_val n, coe_val (m * n)]
    exact map_mul primeVal.extend m n
  exact_mod_cast h

@[simp] lemma val_atom (i : ℕ) : val (atom i) = Nat.nth Nat.Prime i := by
  rw [val, toFactorization]
  change (Finsupp.mapDomain (Nat.nth Nat.Prime) (Finsupp.single i 1)).prod (· ^ ·) = _
  rw [Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp)]
  simp

@[simp] lemma val_pow (m : FormalProd) (k : ℕ) : val (m ^ k) = val m ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, val_mul, ih]

/-- Unique factorisation, one direction: `val` recovers the exponent vector. -/
lemma factorization_val (m : FormalProd) : (val m).factorization = toFactorization m :=
  Nat.prod_pow_factorization_eq_self fun _ hp => toFactorization_support_prime hp

lemma val_injective : Function.Injective val := fun _ _ h =>
  toFactorization_injective (by rw [← factorization_val, ← factorization_val, h])

/-- Unique factorisation, other direction: every positive integer is represented. -/
lemma exists_val_eq {n : ℕ} (hn : 0 < n) : ∃ m, val m = n := by
  have hsub : ↑(n.factorization).support ⊆ Set.range (Nat.nth Nat.Prime) := by
    intro p hp
    exact ⟨Nat.count Nat.Prime p, Nat.nth_count (Nat.prime_of_mem_primeFactors hp)⟩
  refine ⟨Multiplicative.ofAdd
    (Finsupp.comapDomain _ n.factorization nth_prime_injective.injOn), ?_⟩
  rw [val, toFactorization]
  change (Finsupp.mapDomain (Nat.nth Nat.Prime)
    (Finsupp.comapDomain _ n.factorization nth_prime_injective.injOn)).prod (· ^ ·) = n
  rw [Finsupp.mapDomain_comapDomain _ nth_prime_injective _ hsub]
  exact Nat.prod_factorization_pow_eq_self hn.ne'

/-! ## Non-vacuity -/

/-- `val`, shifted down by one, is a bijection from formal products to `ℕ`. -/
noncomputable def modelEquiv : FormalProd ≃ ℕ :=
  Equiv.ofBijective (fun m => val m - 1) <| by
    constructor
    · intro a b hab
      simp only at hab
      have ha := val_pos a
      have hb := val_pos b
      exact val_injective (by omega)
    · intro n
      obtain ⟨m, hm⟩ := exists_val_eq (n := n + 1) (Nat.succ_pos n)
      exact ⟨m, show val m - 1 = n by omega⟩

lemma primeVal_extend_eq_modelEquiv (m : FormalProd) :
    primeVal.extend m = (modelEquiv m : ℝ) + 1 := by
  rw [← coe_val m]
  have hval : (modelEquiv m : ℕ) = val m - 1 := rfl
  have := val_pos m
  rw [hval]
  push_cast [Nat.cast_sub (by omega : 1 ≤ val m)]
  ring

/-- **The hypothesis of the rigidity theorem is satisfiable.** The intended valuation -- the
`i`-th abstract prime sent to the `i`-th ordinary prime -- is ζ-normalized. So
`eq_nth_prime_of_isZetaNormalized` is not vacuously true. -/
theorem primeVal_isZetaNormalized : IsZetaNormalized primeVal :=
  isZetaNormalized_of_equiv modelEquiv primeVal_extend_eq_modelEquiv

end ZetaRigidity

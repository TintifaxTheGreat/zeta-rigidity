/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Primes

/-!
# The unknown valuation

A `Valuation` assigns to each abstract prime a real number `> 1`, strictly increasingly. It
extends uniquely and multiplicatively to all of `FormalProd` (`Valuation.extend`), which is the
map the ζ-condition will later pin down.

Nothing here assumes the values are integers, or indeed related to the ordinary primes at all:
that is precisely what the rigidity theorem has to prove.
-/

namespace ZetaRigidity

open scoped BigOperators

/-- An assignment of a real magnitude `> 1` to each abstract prime, strictly increasing in the
canonical ordering of the primes. -/
structure Valuation where
  /-- The value of the `i`-th abstract prime. -/
  toFun : ℕ → ℝ
  /-- Every prime has magnitude greater than `1`. -/
  one_lt' : ∀ i, 1 < toFun i
  /-- The canonical ordering of the primes is respected. -/
  strictMono' : StrictMono toFun

namespace Valuation

instance : CoeFun Valuation (fun _ => ℕ → ℝ) := ⟨toFun⟩

variable (v : Valuation)

lemma one_lt (i : ℕ) : 1 < v i := v.one_lt' i

lemma pos (i : ℕ) : 0 < v i := lt_trans one_pos (v.one_lt i)

lemma strictMono : StrictMono v := v.strictMono'

/-- The multiplicative extension of `v` to all formal products: a formal product is sent to the
product of its primes' values, with multiplicity. -/
noncomputable def extend : FormalProd →* ℝ where
  toFun m := (Multiplicative.toAdd m).prod fun i k => v i ^ k
  map_one' := by simp
  map_mul' _ _ := Finsupp.prod_add_index' (by simp) (by simp [pow_add])

@[simp] lemma extend_one : v.extend 1 = 1 := map_one _

@[simp] lemma extend_mul (m n : FormalProd) : v.extend (m * n) = v.extend m * v.extend n :=
  map_mul _ _ _

@[simp] lemma extend_atom (i : ℕ) : v.extend (atom i) = v i := by
  change (Finsupp.single i 1).prod (fun j k => v j ^ k) = v i
  rw [Finsupp.prod_single_index] <;> simp

/-- Every formal product has magnitude at least `1`. -/
lemma one_le_extend (m : FormalProd) : 1 ≤ v.extend m :=
  Finset.one_le_prod₀ fun i _ => one_le_pow₀ (v.one_lt i).le

lemma extend_pos (m : FormalProd) : 0 < v.extend m :=
  lt_of_lt_of_le one_pos (v.one_le_extend m)

/-- Only the empty product has magnitude `1`; every nontrivial formal product is strictly
bigger. This is what makes `1` the least element of the reconstructed order. -/
lemma one_lt_extend {m : FormalProd} (hm : m ≠ 1) : 1 < v.extend m := by
  obtain ⟨i, hi⟩ : (Multiplicative.toAdd m).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun h => hm (Multiplicative.toAdd.injective h)
  change 1 < (Multiplicative.toAdd m).prod fun j k => v j ^ k
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hi]
  have h1 : 1 < v i ^ (Multiplicative.toAdd m) i :=
    one_lt_pow₀ (v.one_lt i) (Finsupp.mem_support_iff.mp hi)
  have h2 : (1 : ℝ) ≤ ∏ j ∈ (Multiplicative.toAdd m).support.erase i,
      v j ^ (Multiplicative.toAdd m) j :=
    Finset.one_le_prod₀ fun j _ => one_le_pow₀ (v.one_lt j).le
  nlinarith

lemma extend_eq_one_iff {m : FormalProd} : v.extend m = 1 ↔ m = 1 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hm
  exact absurd h (v.one_lt_extend hm).ne'

end Valuation

end ZetaRigidity

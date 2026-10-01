/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Model

/-!
# The reconstructed order, and what it costs

Once magnitude is recovered, formal products carry a total order and "twin primes" can be stated
structurally -- no addition appears in the definition:

    `Twin P Q` : `P` and `Q` are prime elements, no prime element lies strictly between them,
                 and exactly one element lies strictly between them.

The point of this file is `twin_iff`, which proves this structural definition is **equivalent** to
the classical one, `val Q = val P + 2`. That is worth having for two opposite reasons.

It confirms the translation is faithful: the structural definition really does pick out twin
primes, and nothing was lost.

It also makes concrete the caveat in `ZetaRigidity/Rigidity.lean`. The structural definition avoids
*writing* `+ 2`, but it is interdefinable with it, so the twin prime conjecture in this language
is the classical conjecture, not an easier one. Addition was not eliminated; it was relocated
into the magnitude order. (By Julia Robinson's theorem addition is in fact first-order definable
from multiplication together with this order, so this is an instance of a general phenomenon
rather than an artefact of the definition chosen here.)

Everything here is stated for the concrete model of `ZetaRigidity/Model.lean`; by rigidity every
ζ-normalized valuation is isomorphic to that model.
-/

namespace ZetaRigidity

/-- The reconstructed magnitude order: formal products compared by their recovered value. -/
def MLt (m n : FormalProd) : Prop := val m < val n

/-- `R` lies strictly between `P` and `Q` in the reconstructed order. -/
def Between (P Q R : FormalProd) : Prop := MLt P R ∧ MLt R Q

/-- **Twin primes, stated without addition.** Two prime elements with no prime element strictly
between them, and exactly one element of any kind strictly between them. -/
def Twin (P Q : FormalProd) : Prop :=
  IsPrimeElt P ∧ IsPrimeElt Q ∧
  (∀ R, IsPrimeElt R → ¬ Between P Q R) ∧
  (∃! R, Between P Q R)

/-! ## Basic dictionary between the monoid and the integers -/

/-- Prime elements of the monoid are exactly those of prime value. -/
lemma isPrimeElt_iff {m : FormalProd} : IsPrimeElt m ↔ (val m).Prime := by
  refine ⟨fun ⟨i, hi⟩ => by rw [hi, val_atom]; exact nth_prime_prime i, fun hp => ?_⟩
  have h1 : toFactorization m = Finsupp.single (val m) 1 := by
    rw [← factorization_val m, hp.factorization]
  refine ⟨Nat.count Nat.Prime (val m), toFactorization_injective ?_⟩
  rw [h1, toFactorization]
  change _ = Finsupp.mapDomain (Nat.nth Nat.Prime) (Finsupp.single _ 1)
  rw [Finsupp.mapDomain_single, Nat.nth_count hp]

/-- Every value strictly between two others is attained by exactly one formal product. -/
lemma exists_unique_val {n : ℕ} (hn : 0 < n) : ∃! R, val R = n := by
  obtain ⟨R, hR⟩ := exists_val_eq hn
  exact ⟨R, hR, fun S hS => val_injective (by rw [hS, hR])⟩

/-! ## The translation theorem -/

/-- **The structural definition of twin primes is the classical one.** -/
theorem twin_iff {P Q : FormalProd} :
    Twin P Q ↔ (val P).Prime ∧ (val Q).Prime ∧ val Q = val P + 2 := by
  constructor
  · rintro ⟨hP, hQ, -, R, ⟨hPR, hRQ⟩, huniq⟩
    simp only [MLt] at hPR hRQ
    refine ⟨isPrimeElt_iff.mp hP, isPrimeElt_iff.mp hQ, ?_⟩
    -- `R` sits strictly between, so the gap is at least `2`; were it more, there would be two
    -- distinct elements in between, contradicting uniqueness.
    by_contra hgap
    have hQbig : val P + 3 ≤ val Q := by omega
    obtain ⟨S, hS⟩ := exists_val_eq (n := val P + 1) (by omega)
    obtain ⟨T, hT⟩ := exists_val_eq (n := val P + 2) (by omega)
    have hSb : Between P Q S := ⟨by simp only [MLt]; omega, by simp only [MLt]; omega⟩
    have hTb : Between P Q T := ⟨by simp only [MLt]; omega, by simp only [MLt]; omega⟩
    have hST : S = T := (huniq S hSb).trans (huniq T hTb).symm
    rw [hST, hT] at hS
    omega
  · rintro ⟨hP, hQ, hgap⟩
    -- `val P` cannot be `2`, else `val Q = 4` would have to be prime.
    have hP2 : val P ≠ 2 := by
      intro h
      rw [h] at hgap
      rw [hgap] at hQ
      norm_num at hQ
    -- so `val P` is odd, making `val P + 1` even and `> 2`, hence composite.
    have hmid : ¬ (val P + 1).Prime := by
      intro hmp
      obtain ⟨k, hk⟩ := hP.odd_of_ne_two hP2
      have h2 : (2 : ℕ) ∣ val P + 1 := ⟨k + 1, by omega⟩
      have h3 := hmp.eq_one_or_self_of_dvd 2 h2
      have h4 := hP.two_le
      omega
    refine ⟨isPrimeElt_iff.mpr hP, isPrimeElt_iff.mpr hQ, ?_, ?_⟩
    · rintro R hR ⟨h1, h2⟩
      simp only [MLt] at h1 h2
      have hRv : val R = val P + 1 := by omega
      exact hmid (hRv ▸ isPrimeElt_iff.mp hR)
    · obtain ⟨R, hR⟩ := exists_val_eq (n := val P + 1) (by omega)
      refine ⟨R, ⟨by simp only [MLt]; omega, by simp only [MLt]; omega⟩, fun S hS => ?_⟩
      obtain ⟨h1, h2⟩ := hS
      simp only [MLt] at h1 h2
      exact val_injective (by omega)

end ZetaRigidity

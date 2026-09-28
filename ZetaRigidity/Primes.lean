/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import Mathlib

/-!
# Abstract primes and formal products

The starting point of the ζ-rigidity construction: an abstract set of primes equipped with a
distinguished least element, a successor, and an induction principle -- that is, exactly the
Peano axioms, which is what "order type ω" amounts to.

The first result of this file is that such a structure carries no information: any `P` satisfying
these axioms is in bijection with `ℕ` (`PrimeSequence.equivNat`). We therefore state the axioms
once, discharge them once, and work concretely with `ℕ` from then on, rather than paying for the
abstraction in every downstream proof.

From the primes we build `FormalProd`, the free commutative monoid of finite formal products.
Multiplication is primitive and unique factorisation is *definitional*: an element simply **is**
its exponent vector.
-/

namespace ZetaRigidity

/-- An abstract sequence of primes: a least element, a successor, and an induction principle.
These are the Peano axioms, so this pins the order type to ω. -/
structure PrimeSequence (P : Type*) where
  /-- The distinguished least prime. -/
  least : P
  /-- The successor relation, as a function. -/
  succ : P → P
  /-- The least prime is not a successor. -/
  succ_ne_least : ∀ p, succ p ≠ least
  /-- Successor is injective. -/
  succ_injective : Function.Injective succ
  /-- Induction: every element is reached from `least` by iterating `succ`. -/
  induction : ∀ motive : P → Prop, motive least →
    (∀ p, motive p → motive (succ p)) → ∀ p, motive p

namespace PrimeSequence

variable {P : Type*} (hP : PrimeSequence P)

/-- The canonical map `ℕ → P` sending `n` to the `n`-th prime. Written via `Nat.rec` rather
than by pattern matching so that the two equations below hold by `rfl`. -/
def ofNat (n : ℕ) : P := Nat.rec hP.least (fun _ p => hP.succ p) n

@[simp] lemma ofNat_zero : hP.ofNat 0 = hP.least := rfl

@[simp] lemma ofNat_succ (n : ℕ) : hP.ofNat (n + 1) = hP.succ (hP.ofNat n) := rfl

lemma ofNat_injective : Function.Injective hP.ofNat := by
  intro m
  induction m with
  | zero =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n => exact absurd hn.symm (hP.succ_ne_least _)
  | succ m ih =>
    intro n hn
    cases n with
    | zero => exact absurd hn (hP.succ_ne_least _)
    | succ n => exact congrArg (· + 1) (ih (hP.succ_injective hn))

lemma ofNat_surjective : Function.Surjective hP.ofNat := by
  refine hP.induction (fun p => ∃ n, hP.ofNat n = p) ⟨0, rfl⟩ ?_
  rintro p ⟨n, rfl⟩
  exact ⟨n + 1, rfl⟩

/-- **Any abstract prime sequence is just `ℕ`.** The axioms of `PrimeSequence` carry no
information beyond the order type, so nothing is lost by working with `ℕ` downstream. -/
noncomputable def equivNat : ℕ ≃ P :=
  Equiv.ofBijective hP.ofNat ⟨hP.ofNat_injective, hP.ofNat_surjective⟩

end PrimeSequence

/-- `ℕ` itself is an abstract prime sequence, so the axioms are not vacuous. -/
def natPrimeSequence : PrimeSequence ℕ where
  least := 0
  succ := (· + 1)
  succ_ne_least := fun _ => Nat.succ_ne_zero _
  succ_injective := fun _ _ h => by simpa using h
  induction := fun _ h0 hs => Nat.rec h0 hs

/-! ## Formal products

The free commutative monoid on the primes. An element is a finitely-supported exponent vector;
multiplication of formal products is addition of exponents, so we wrap in `Multiplicative` to
keep multiplication -- the primitive operation of the whole construction -- written as `*`.
-/

/-- Finite formal products of abstract primes: the free commutative monoid on `ℕ`. -/
abbrev FormalProd := Multiplicative (ℕ →₀ ℕ)

/-- The formal product consisting of the single prime `i`. These are the atoms. -/
noncomputable def atom (i : ℕ) : FormalProd := Multiplicative.ofAdd (Finsupp.single i 1)

/-- The exponent of the prime `i` in a formal product. -/
def expo (m : FormalProd) (i : ℕ) : ℕ := Multiplicative.toAdd m i

@[simp] lemma expo_atom (i j : ℕ) : expo (atom i) j = if i = j then 1 else 0 := by
  simp [expo, atom, Finsupp.single_apply]

@[simp] lemma expo_mul (m n : FormalProd) (i : ℕ) : expo (m * n) i = expo m i + expo n i := rfl

@[simp] lemma expo_one (i : ℕ) : expo 1 i = 0 := rfl

/-- Formal products are determined by their exponents: unique factorisation, definitionally. -/
lemma ext_expo {m n : FormalProd} (h : ∀ i, expo m i = expo n i) : m = n :=
  Multiplicative.toAdd.injective (Finsupp.ext h)

lemma atom_injective : Function.Injective atom := fun _ _ h =>
  Finsupp.single_left_injective one_ne_zero (Multiplicative.toAdd.injective h)

/-! ### Degree

The total number of prime factors, with multiplicity. This is the tool for showing that the
atoms really are atoms -- needed later to see that a multiplicative bijection onto `ℤ_{>0}`
must carry abstract primes to ordinary primes.
-/

/-- The total number of prime factors of a formal product, counted with multiplicity. -/
noncomputable def degree (m : FormalProd) : ℕ := (Multiplicative.toAdd m).sum fun _ k => k

@[simp] lemma degree_one : degree 1 = 0 := rfl

@[simp] lemma degree_mul (m n : FormalProd) : degree (m * n) = degree m + degree n :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] lemma degree_atom (i : ℕ) : degree (atom i) = 1 :=
  Finsupp.sum_single_index rfl

lemma degree_eq_zero_iff {m : FormalProd} : degree m = 0 ↔ m = 1 := by
  refine ⟨fun h => ext_expo fun i => ?_, fun h => by rw [h, degree_one]⟩
  rw [expo_one]
  by_contra hi
  exact hi (Finset.sum_eq_zero_iff.mp h i (Finsupp.mem_support_iff.mpr hi))

lemma atom_ne_one (i : ℕ) : atom i ≠ 1 := fun h => by
  simpa [h] using (degree_atom i).symm

/-- If the prime `i` occurs in `m`, then `m` factors as `atom i` times something. -/
lemma exists_eq_atom_mul {m : FormalProd} {i : ℕ} (hi : 0 < expo m i) :
    ∃ m', m = atom i * m' :=
  ⟨Multiplicative.ofAdd (Multiplicative.toAdd m - Finsupp.single i 1),
    Multiplicative.toAdd.injective
      (add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)).symm⟩

/-- A formal product other than the empty one contains some prime. -/
lemma exists_expo_pos {m : FormalProd} (hm : m ≠ 1) : ∃ i, 0 < expo m i := by
  by_contra h
  push Not at h
  exact hm (ext_expo fun i => by simpa using Nat.le_zero.mp (h i))

/-- The atoms are irreducible: a formal product equal to a single prime has a trivial factor.
This is unique factorisation doing its work. -/
lemma eq_one_or_eq_one_of_mul_eq_atom {m n : FormalProd} {i : ℕ} (h : m * n = atom i) :
    m = 1 ∨ n = 1 := by
  have hd : degree m + degree n = 1 := by rw [← degree_mul, h, degree_atom]
  rcases Nat.eq_zero_or_pos (degree m) with h0 | h0
  · exact Or.inl (degree_eq_zero_iff.mp h0)
  · exact Or.inr (degree_eq_zero_iff.mp (by omega))

end ZetaRigidity

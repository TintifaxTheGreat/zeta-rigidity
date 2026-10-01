/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import Mathlib

/-!
# Abstract primes and formal products

This file sets up the objects the rigidity theorem is about.

A `PrimeSequence` is an abstract set of primes with a least element, a successor and an induction
principle. These are the Peano axioms, so they fix the order type to ω and nothing else.
`PrimeSequence.equivNat` shows that any such structure is in bijection with `ℕ`, so the axioms
are stated and discharged once and the rest of the development works with `ℕ`.

`FormalProd` is the free commutative monoid on the primes. An element is its exponent vector, so
multiplication is the primitive operation and unique factorisation holds by definition. Two
exponent vectors that differ are different elements even if a valuation later assigns them the
same real number; in the theory of generalized prime systems this is the convention that the
generalized integers form a multiset.

## Main results

* `PrimeSequence.equivNat`: the prime axioms determine the index set up to bijection.
* `irreducible_iff_isPrimeElt`: the atoms are exactly the irreducible elements.
* `lift` and `hom_ext`: the universal property of the free commutative monoid.
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

/-- Any abstract prime sequence is in bijection with `ℕ`. The axioms carry no information
beyond the order type, so nothing is lost by working with `ℕ` downstream. -/
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

The free commutative monoid on the primes. An element is a finitely supported exponent vector.
Multiplication of formal products is addition of exponents, so the type is wrapped in
`Multiplicative` to keep the primitive operation written as `*`.
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

@[simp] lemma expo_pow (m : FormalProd) (k i : ℕ) : expo (m ^ k) i = k * expo m i := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, expo_mul, ih]; ring

/-- Formal products are determined by their exponents. This is unique factorisation, holding by
definition rather than as a theorem. -/
lemma ext_expo {m n : FormalProd} (h : ∀ i, expo m i = expo n i) : m = n :=
  Multiplicative.toAdd.injective (Finsupp.ext h)

lemma atom_injective : Function.Injective atom := fun _ _ h =>
  Finsupp.single_left_injective one_ne_zero (Multiplicative.toAdd.injective h)

/-! ### Degree

The number of prime factors, with multiplicity. Used to show the atoms are irreducible, which in
turn shows a multiplicative bijection onto `ℤ_{>0}` carries abstract primes to ordinary primes.
-/

/-- The total number of prime factors of a formal product, counted with multiplicity. -/
noncomputable def degree (m : FormalProd) : ℕ := (Multiplicative.toAdd m).sum fun _ k => k

@[simp] lemma degree_one : degree 1 = 0 := rfl

@[simp] lemma degree_mul (m n : FormalProd) : degree (m * n) = degree m + degree n :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

@[simp] lemma degree_atom (i : ℕ) : degree (atom i) = 1 :=
  Finsupp.sum_single_index rfl

@[simp] lemma degree_pow (m : FormalProd) (k : ℕ) : degree (m ^ k) = k * degree m := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, degree_mul, ih]; ring

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

/-- If a product of two formal products is an atom, one of the factors is empty. -/
lemma eq_one_or_eq_one_of_mul_eq_atom {m n : FormalProd} {i : ℕ} (h : m * n = atom i) :
    m = 1 ∨ n = 1 := by
  have hd : degree m + degree n = 1 := by rw [← degree_mul, h, degree_atom]
  rcases Nat.eq_zero_or_pos (degree m) with h0 | h0
  · exact Or.inl (degree_eq_zero_iff.mp h0)
  · exact Or.inr (degree_eq_zero_iff.mp (by omega))

/-! ## Atoms without reference to the indexing

`IsPrimeElt` identifies an atom by naming its index. The two lemmas below characterise the same
elements intrinsically, by degree and by irreducibility. The second is what lets an automorphism
be seen to permute the primes: an isomorphism does not see indices, but it preserves
irreducibility.
-/

/-- A prime element is an atom of the monoid, that is, one of the abstract primes. -/
def IsPrimeElt (m : FormalProd) : Prop := ∃ i, m = atom i

lemma isPrimeElt_atom (i : ℕ) : IsPrimeElt (atom i) := ⟨i, rfl⟩

/-- The atoms are exactly the elements of degree one. -/
lemma degree_eq_one_iff {m : FormalProd} : degree m = 1 ↔ IsPrimeElt m := by
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => by rw [hi, degree_atom]⟩
  have hm : m ≠ 1 := fun hm => by simp [hm] at h
  obtain ⟨i, hi⟩ := exists_expo_pos hm
  obtain ⟨m', hm'⟩ := exists_eq_atom_mul hi
  refine ⟨i, ?_⟩
  have : degree m' = 0 := by
    have := degree_mul (atom i) m'
    rw [← hm', h, degree_atom] at this
    omega
  rw [hm', degree_eq_zero_iff.mp this, mul_one]

/-- The only unit is the empty product: a free commutative monoid has no invertible elements
beyond `1`. -/
lemma isUnit_iff {m : FormalProd} : IsUnit m ↔ m = 1 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun h => h ▸ isUnit_one⟩
  have h1 : degree (↑u : FormalProd) + degree (↑u⁻¹ : FormalProd) = 0 := by
    rw [← degree_mul, u.mul_inv, degree_one]
  rw [← hu]
  exact degree_eq_zero_iff.mp (by omega)

/-- The atoms are exactly the irreducible elements. This description mentions neither the
indexing nor the degree, so it transports along any monoid isomorphism. -/
lemma irreducible_iff_isPrimeElt {m : FormalProd} : Irreducible m ↔ IsPrimeElt m := by
  constructor
  · rintro ⟨hu, hfac⟩
    have hm : m ≠ 1 := fun h => hu (h ▸ isUnit_one)
    obtain ⟨i, hi⟩ := exists_expo_pos hm
    obtain ⟨m', hm'⟩ := exists_eq_atom_mul hi
    rcases hfac hm' with h | h
    · exact absurd (isUnit_iff.mp h) (atom_ne_one i)
    · exact ⟨i, by rw [hm', isUnit_iff.mp h, mul_one]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨fun h => atom_ne_one i (isUnit_iff.mp h), fun a b hab => ?_⟩
    rcases eq_one_or_eq_one_of_mul_eq_atom hab.symm with h | h
    · exact Or.inl (isUnit_iff.mpr h)
    · exact Or.inr (isUnit_iff.mpr h)

/-! ## The universal property

`FormalProd` is free on the atoms: a monoid homomorphism out of it may be prescribed arbitrarily
on the atoms, and is then determined. Mathlib has no `FreeCommMonoid`, so this is stated here.

`Valuation.extend` and the characters of `ZetaRigidity/Extensions/Characters.lean` are both
instances of `lift`, and `autEquivPerm` is proved using `hom_ext`.
-/

/-- A single prime power, as a power of an atom. -/
lemma ofAdd_single (i k : ℕ) :
    (Multiplicative.ofAdd (Finsupp.single i k) : FormalProd) = atom i ^ k := by
  apply Multiplicative.toAdd.injective
  change Finsupp.single i k = k • Finsupp.single i 1
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

variable {M : Type*} [CommMonoid M]

/-- Any assignment of values to the abstract primes extends to a monoid homomorphism. -/
noncomputable def lift (z : ℕ → M) : FormalProd →* M where
  toFun m := (Multiplicative.toAdd m).prod fun i k => z i ^ k
  map_one' := by simp
  map_mul' _ _ := Finsupp.prod_add_index' (by simp) (by simp [pow_add])

@[simp] lemma lift_atom (z : ℕ → M) (i : ℕ) : lift z (atom i) = z i := by
  change (Finsupp.single i 1).prod (fun j k => z j ^ k) = z i
  rw [Finsupp.prod_single_index] <;> simp

/-- Two homomorphisms that agree on the atoms are equal, since every formal product is a
product of atoms. -/
lemma hom_ext {f g : FormalProd →* M} (h : ∀ i, f (atom i) = g (atom i)) : f = g := by
  refine MonoidHom.ext fun m => ?_
  suffices hall : ∀ p : ℕ →₀ ℕ, f (Multiplicative.ofAdd p) = g (Multiplicative.ofAdd p) from
    hall (Multiplicative.toAdd m)
  intro p
  induction p using Finsupp.induction_linear with
  | zero =>
    change f 1 = g 1
    rw [map_one, map_one]
  | add a b ha hb =>
    change f (Multiplicative.ofAdd a * Multiplicative.ofAdd b)
      = g (Multiplicative.ofAdd a * Multiplicative.ofAdd b)
    rw [map_mul, map_mul, ha, hb]
  | single i k => rw [ofAdd_single, map_pow, map_pow, h i]

lemma lift_unique {z : ℕ → M} {f : FormalProd →* M} (h : ∀ i, f (atom i) = z i) : f = lift z :=
  hom_ext fun i => by rw [h i, lift_atom]

end ZetaRigidity

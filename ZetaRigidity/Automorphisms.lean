/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Primes

/-!
# The tame side: multiplication alone sees no individual prime

`ZetaRigidity/Rigidity.lean` proves that the ζ-condition pins the valuation down completely. That
is only half of a contrast; this file proves the other half, and it is the half that says why the
first one is worth anything.

## Main result

`autEquivPerm : MulAut FormalProd ≃* Equiv.Perm ℕ`

The automorphism group of the free commutative monoid is the *full* permutation group of its
atoms. Every permutation of the abstract primes extends to a symmetry of the whole multiplicative
structure, and every symmetry arises this way. So in `(ℤ_{>0}, ×)` no individual prime is
distinguishable from any other by multiplicative means: any statement about "the prime `2`" is
carried by an automorphism to the same statement about `5`, or about the `10^100`-th prime.

This is what "ζ rigidifies the multiplicative monoid" is a statement *against*. Before the ζ
condition the symmetry group is as large as it could possibly be; afterwards the valuation is
unique (`ZetaRigidity/Rigidity.lean`). Nothing in between is available, because a monoid
isomorphism must carry irreducibles to irreducibles and there is no further structure to preserve.

## Why this file imports nothing analytic

It deliberately depends on `Primes.lean` only. The statement is about the bare monoid, and mixing
in the recovered order or the concrete model would obscure that the non-rigidity is present
*before* any numerical content is introduced.
-/

namespace ZetaRigidity

/-! ## An automorphism permutes the atoms

The key point is that `IsPrimeElt` has an intrinsic characterisation --
`irreducible_iff_isPrimeElt` in `ZetaRigidity/Primes.lean` -- so it transports along any monoid
isomorphism even though the isomorphism cannot see the indexing.
-/

lemma aut_eq_one_iff (φ : MulAut FormalProd) {m : FormalProd} : φ m = 1 ↔ m = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  rw [← φ.symm_apply_apply m, h, map_one]

lemma isUnit_aut_iff (φ : MulAut FormalProd) {m : FormalProd} : IsUnit (φ m) ↔ IsUnit m := by
  rw [isUnit_iff, isUnit_iff, aut_eq_one_iff]

/-- A monoid automorphism carries atoms to atoms. -/
lemma isPrimeElt_aut (φ : MulAut FormalProd) {m : FormalProd} (hm : IsPrimeElt m) :
    IsPrimeElt (φ m) := by
  rw [← irreducible_iff_isPrimeElt] at hm ⊢
  refine ⟨fun h => hm.not_isUnit ((isUnit_aut_iff φ).mp h), fun a b hab => ?_⟩
  have hm' : m = φ.symm a * φ.symm b := by rw [← map_mul, ← hab, φ.symm_apply_apply]
  have key : ∀ x : FormalProd, IsUnit (φ.symm x) → IsUnit x := fun x hx => by
    rw [← φ.apply_symm_apply x]
    exact (isUnit_aut_iff φ).mpr hx
  rcases hm.isUnit_or_isUnit hm' with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key b h)

/-- The index of the atom that `φ` sends the `i`-th atom to. -/
noncomputable def autIndex (φ : MulAut FormalProd) (i : ℕ) : ℕ :=
  (isPrimeElt_aut φ (isPrimeElt_atom i)).choose

lemma autIndex_spec (φ : MulAut FormalProd) (i : ℕ) : φ (atom i) = atom (autIndex φ i) :=
  (isPrimeElt_aut φ (isPrimeElt_atom i)).choose_spec

lemma autIndex_symm_autIndex (φ : MulAut FormalProd) (i : ℕ) :
    autIndex φ.symm (autIndex φ i) = i := by
  apply atom_injective
  rw [← autIndex_spec, ← autIndex_spec, φ.symm_apply_apply]

/-- **An automorphism is a permutation of the primes.** -/
noncomputable def toPerm (φ : MulAut FormalProd) : Equiv.Perm ℕ where
  toFun := autIndex φ
  invFun := autIndex φ.symm
  left_inv := autIndex_symm_autIndex φ
  right_inv i := by
    have h := autIndex_symm_autIndex φ.symm i
    rwa [φ.symm_symm] at h

@[simp] lemma toPerm_apply (φ : MulAut FormalProd) (i : ℕ) : toPerm φ i = autIndex φ i := rfl

/-! ## Every permutation is an automorphism -/

/-- **A permutation of the primes is an automorphism.** Relabelling the generators of a free
commutative monoid is a monoid isomorphism -- this is the direction that makes the symmetry group
as large as possible. -/
def ofPerm (σ : Equiv.Perm ℕ) : MulAut FormalProd where
  toFun m := Multiplicative.ofAdd (Finsupp.equivMapDomain σ (Multiplicative.toAdd m))
  invFun m := Multiplicative.ofAdd (Finsupp.equivMapDomain σ.symm (Multiplicative.toAdd m))
  left_inv m := by
    change Multiplicative.ofAdd
      (Finsupp.equivMapDomain σ.symm (Finsupp.equivMapDomain σ (Multiplicative.toAdd m))) = m
    rw [← Finsupp.equivMapDomain_trans, Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]
    rfl
  right_inv m := by
    change Multiplicative.ofAdd
      (Finsupp.equivMapDomain σ (Finsupp.equivMapDomain σ.symm (Multiplicative.toAdd m))) = m
    rw [← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]
    rfl
  map_mul' m n := by
    apply Multiplicative.toAdd.injective
    ext i
    change Finsupp.equivMapDomain σ (Multiplicative.toAdd m + Multiplicative.toAdd n) i
      = Finsupp.equivMapDomain σ (Multiplicative.toAdd m) i
        + Finsupp.equivMapDomain σ (Multiplicative.toAdd n) i
    simp [Finsupp.equivMapDomain_apply]

@[simp] lemma ofPerm_atom (σ : Equiv.Perm ℕ) (i : ℕ) : ofPerm σ (atom i) = atom (σ i) := by
  change Multiplicative.ofAdd (Finsupp.equivMapDomain σ (Finsupp.single i 1))
    = Multiplicative.ofAdd (Finsupp.single (σ i) 1)
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]

@[simp] lemma autIndex_ofPerm (σ : Equiv.Perm ℕ) (i : ℕ) : autIndex (ofPerm σ) i = σ i :=
  atom_injective (by rw [← autIndex_spec, ofPerm_atom])

/-! ## The two constructions are inverse -/

/-- A formal product is a product of atoms, so two automorphisms agreeing on atoms are equal.
This is `hom_ext` (`ZetaRigidity/Primes.lean`) read through the forgetful map from isomorphisms
to homomorphisms. -/
lemma aut_ext {φ ψ : MulAut FormalProd} (h : ∀ i, φ (atom i) = ψ (atom i)) : φ = ψ :=
  MulEquiv.toMonoidHom_injective (hom_ext (M := FormalProd) h)

/-- **The automorphism group of the free commutative monoid is the full permutation group of its
atoms.** -/
noncomputable def autEquivPerm : MulAut FormalProd ≃* Equiv.Perm ℕ where
  toFun := toPerm
  invFun := ofPerm
  left_inv φ := aut_ext fun i => by rw [ofPerm_atom, toPerm_apply, ← autIndex_spec]
  right_inv σ := Equiv.ext fun i => by rw [toPerm_apply, autIndex_ofPerm]
  map_mul' φ ψ := by
    refine Equiv.ext fun i => ?_
    change autIndex (φ * ψ) i = autIndex φ (autIndex ψ i)
    apply atom_injective
    rw [← autIndex_spec, ← autIndex_spec, ← autIndex_spec]
    rfl

/-! ## What it means

Two corollaries, stated because they are the sentences the README wants to be able to make.
-/

/-- Any prime can be moved to any other by a symmetry of the multiplicative structure: no
individual prime is definable from multiplication alone. -/
theorem exists_aut_map_atom (i j : ℕ) : ∃ φ : MulAut FormalProd, φ (atom i) = atom j :=
  ⟨ofPerm (Equiv.swap i j), by rw [ofPerm_atom, Equiv.swap_apply_left]⟩

/-- The symmetry group is not merely large but *maximal*: every relabelling of the primes is
realized, so multiplication imposes no constraint on how they may be permuted. -/
theorem toPerm_surjective : Function.Surjective toPerm :=
  fun σ => ⟨ofPerm σ, autEquivPerm.right_inv σ⟩

end ZetaRigidity

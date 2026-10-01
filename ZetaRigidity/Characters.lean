/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Valuation

/-!
# The dual group is the infinite torus

A character of `FormalProd` is a monoid homomorphism into the circle group. By freeness
(`hom_ext` and `lift` in `ZetaRigidity/Primes.lean`) such a thing may be prescribed *arbitrarily*
on the atoms and is then determined, so the dual group is a product of one circle per prime:

`charEquivTorus : (FormalProd →* Circle) ≃* (ℕ → Circle)`

This is the exact analogue of `autEquivPerm` (`ZetaRigidity/Automorphisms.lean`) -- the same
freeness fact, with `Equiv.Perm ℕ` replaced by the infinite torus `𝕋^∞`.

## The Bohr correspondence

The point of the identification is that it turns Dirichlet series into power series. Write
`z_i` for the `i`-th circle coordinate. A character sends the formal product with exponents
`(k_i)` to the *monomial* `∏ z_i ^ k_i`, so a series `∑_m a_m χ(m)` is literally a power series
on `𝕋^∞` in the variables `z_i`. Under `bohrChar` below, the vertical shift `s ↦ s + it` of a
Dirichlet series corresponds to the point `(v i ^ (-it))_i` of the torus. This is the Bohr
correspondence, the basis of the theory of Hardy spaces of Dirichlet series
(Hedenmalm--Lindqvist--Seip). None of that theory is developed here; this file only builds the
index-level identification it rests on.

> The attribution of the correspondence to Bohr, and of the Hardy-space theory to
> Hedenmalm--Lindqvist--Seip, is background context and has not been checked against the primary
> sources. Nothing below depends on it.
-/

namespace ZetaRigidity

/-! ## Characters -/

/-- A character of the free commutative monoid on the primes. -/
abbrev Character := FormalProd →* Circle

/-- **The dual group is the infinite torus.** A character may take any value whatsoever on each
prime, independently -- which is the multiplicative counterpart of `autEquivPerm`. -/
noncomputable def charEquivTorus : Character ≃* (ℕ → Circle) where
  toFun f i := f (atom i)
  invFun := lift
  left_inv _ := (lift_unique fun _ => rfl).symm
  right_inv z := funext fun i => lift_atom z i
  map_mul' _ _ := rfl

@[simp] lemma charEquivTorus_apply (f : Character) (i : ℕ) : charEquivTorus f i = f (atom i) :=
  rfl

@[simp] lemma charEquivTorus_symm_apply (z : ℕ → Circle) : charEquivTorus.symm z = lift z := rfl

/-- Characters are determined by their values on the primes. -/
lemma character_ext {f g : Character} (h : ∀ i, f (atom i) = g (atom i)) : f = g := hom_ext h

/-! ## The Bohr lift of a vertical shift

For a Beurling system `v` the assignment `m ↦ V(m)^(-it)` is a character, and it is the lift of
`i ↦ v i ^ (-it)`. Under `charEquivTorus` the real parameter `t` therefore names a point of the
infinite torus -- the content of the Bohr correspondence.
-/

/-- The same character written directly, as `m ↦ V(m)^(-it)`. It is a homomorphism because
`log` turns the multiplicativity of `extend` into additivity. -/
noncomputable def logChar (v : Valuation) (t : ℝ) : Character where
  toFun m := Circle.exp (-(t * Real.log (v.extend m)))
  map_one' := by simp
  map_mul' m n := by
    simp only [v.extend_mul]
    rw [Real.log_mul (v.extend_pos m).ne' (v.extend_pos n).ne',
      show -(t * (Real.log (v.extend m) + Real.log (v.extend n)))
        = -(t * Real.log (v.extend m)) + -(t * Real.log (v.extend n)) by ring,
      Circle.exp_add]

/-- The character `m ↦ V(m)^(-it)`, built from its values on the primes. -/
noncomputable def bohrChar (v : Valuation) (t : ℝ) : Character :=
  lift fun i => Circle.exp (-(t * Real.log (v i)))

@[simp] lemma bohrChar_atom (v : Valuation) (t : ℝ) (i : ℕ) :
    bohrChar v t (atom i) = Circle.exp (-(t * Real.log (v i))) :=
  lift_atom _ i

/-- **The Bohr lift.** Prescribing `V(p)^(-it)` on each prime and extending freely gives exactly
`m ↦ V(m)^(-it)`. Both sides are homomorphisms agreeing on the atoms, so `lift_unique` applies;
no induction is needed. -/
theorem bohrChar_eq_logChar (v : Valuation) (t : ℝ) : bohrChar v t = logChar v t :=
  (lift_unique fun i => by
    change Circle.exp (-(t * Real.log (v.extend (atom i)))) = _
    rw [v.extend_atom]).symm

theorem bohrChar_apply (v : Valuation) (t : ℝ) (m : FormalProd) :
    bohrChar v t m = Circle.exp (-(t * Real.log (v.extend m))) := by
  rw [bohrChar_eq_logChar]
  rfl

/-! ## The dual is not trivial

A correspondence is worth nothing if the object it names is a point. These confirm the torus
really is being used.
-/

/-- The character sending the first prime to `-1` and every other prime to `1`. -/
noncomputable def signChar : Character :=
  lift fun i => if i = 0 then Circle.exp Real.pi else 1

@[simp] lemma signChar_atom_zero : signChar (atom 0) = Circle.exp Real.pi := by
  rw [signChar, lift_atom]
  simp

/-- So the dual group is not trivial: some character is not the constant `1`, and hence the
torus coordinate at the first prime is genuinely being used. -/
theorem exists_character_ne_one : ∃ f : Character, f ≠ 1 := by
  refine ⟨signChar, fun h => ?_⟩
  have h0 : signChar (atom 0) = 1 := by rw [h]; rfl
  rw [signChar_atom_zero] at h0
  exact Circle.exp_pi_ne_one h0

/-- **Characters separate the primes from the empty product.** For every prime there is a
character not killing it. -/
theorem exists_character_atom_ne_one (i : ℕ) : ∃ f : Character, f (atom i) ≠ 1 := by
  refine ⟨lift fun j => if j = i then Circle.exp Real.pi else 1, ?_⟩
  rw [lift_atom]
  simpa using Circle.exp_pi_ne_one

end ZetaRigidity

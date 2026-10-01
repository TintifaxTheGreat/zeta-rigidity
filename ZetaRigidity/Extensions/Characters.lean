/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Extensions.ValuationExtras

/-!
# The character group of the monoid of formal products

A character of `FormalProd` is a monoid homomorphism into the circle group. By `lift` and
`hom_ext` (`ZetaRigidity/Primes.lean`) a character may be prescribed arbitrarily on the atoms
and is then determined, so the character group is a product of one circle per prime:

`charEquivTorus : (FormalProd →* Circle) ≃* (ℕ → Circle)`

This is the analogue of `autEquivPerm` (`ZetaRigidity/Automorphisms.lean`), with
`Equiv.Perm ℕ` replaced by the infinite torus.

## Relation to Dirichlet series

Writing `z_i` for the `i`-th circle coordinate, a character sends the formal product with
exponents `(k_i)` to the monomial `∏ z_i ^ k_i`, so a series `∑_m a_m χ(m)` is a power series in
the `z_i`. Under `bohrChar` below, the shift `s ↦ s + it` corresponds to the torus point
`(v i ^ (-it))_i`. This identification is due to Bohr and underlies the theory of Hardy spaces
of Dirichlet series; only the index-level statement is proved here.

> The attributions in the previous paragraph are background and have not been checked against
> primary sources. Nothing below depends on them.
-/

namespace ZetaRigidity

/-! ## Characters -/

/-- A character of the free commutative monoid on the primes. -/
abbrev Character := FormalProd →* Circle

/-- The character group is the infinite torus: a character may take any value on each prime,
independently of the others. -/
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

/-! ## The shift `s ↦ s + it` as a character

For a valuation `v` the assignment `m ↦ V(m)^(-it)` is a character, and it is the lift of
`i ↦ v i ^ (-it)`. Under `charEquivTorus` the parameter `t` therefore names a point of the
infinite torus.
-/

/-- The character `m ↦ V(m)^(-it)` written directly. It is a homomorphism because `log` turns
the multiplicativity of `extend` into additivity. -/
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

/-- Prescribing `V(p)^(-it)` on each prime and extending gives `m ↦ V(m)^(-it)`. Both sides
are homomorphisms agreeing on the atoms, so `lift_unique` applies. -/
theorem bohrChar_eq_logChar (v : Valuation) (t : ℝ) : bohrChar v t = logChar v t :=
  (lift_unique fun i => by
    change Circle.exp (-(t * Real.log (v.extend (atom i)))) = _
    rw [v.extend_atom]).symm

theorem bohrChar_apply (v : Valuation) (t : ℝ) (m : FormalProd) :
    bohrChar v t m = Circle.exp (-(t * Real.log (v.extend m))) := by
  rw [bohrChar_eq_logChar]
  rfl

/-! ## The character group is not trivial -/

/-- The character sending the first prime to `-1` and every other prime to `1`. -/
noncomputable def signChar : Character :=
  lift fun i => if i = 0 then Circle.exp Real.pi else 1

@[simp] lemma signChar_atom_zero : signChar (atom 0) = Circle.exp Real.pi := by
  rw [signChar, lift_atom]
  simp

/-- Some character is not the constant `1`, so the character group is not trivial. -/
theorem exists_character_ne_one : ∃ f : Character, f ≠ 1 := by
  refine ⟨signChar, fun h => ?_⟩
  have h0 : signChar (atom 0) = 1 := by rw [h]; rfl
  rw [signChar_atom_zero] at h0
  exact Circle.exp_pi_ne_one h0

/-- For every prime there is a character that does not send it to `1`. -/
theorem exists_character_atom_ne_one (i : ℕ) : ∃ f : Character, f (atom i) ≠ 1 := by
  refine ⟨lift fun j => if j = i then Circle.exp Real.pi else 1, ?_⟩
  rw [lift_atom]
  simpa using Circle.exp_pi_ne_one

end ZetaRigidity

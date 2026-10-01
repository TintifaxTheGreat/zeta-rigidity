/-
Copyright (c) 2026 Eugen Lindorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugen Lindorfer
-/
import ZetaRigidity.Order

/-!
# Addition was relocated, not eliminated

`ZetaRigidity/Order.lean` observes that once the magnitude order is available alongside
multiplication, ordinary addition comes back: the structural definition of twin primes is
*provably* the classical one. That observation was justified by citing Julia Robinson. This file
replaces the citation with a proof.

## Main results

* `msucc_eq_iff` -- the successor is definable from the order alone: `msucc m` is the least
  element strictly above `m`, with nothing in between.
* `add_definable` -- **addition is definable from multiplication and the order**. Writing `S` for
  the order-defined successor,

      val R = val P + val Q   ↔   S (P·R) · S (Q·R) = S (S (P·Q) · R · R)

  and the right-hand side mentions only `*` and `S`. Since `S` is order-definable, the whole
  condition lives in the language `(×, <)`.

## Provenance

The identity is Robinson's, from J. Robinson, *Definability and decision problems in arithmetic*,
Journal of Symbolic Logic **14** (1949), 98--114, Theorem 1.1: over the positive integers,
addition is first-order definable from multiplication together with successor, and also from
multiplication together with `<`. The particular polynomial form used here,

    (1 + x·z)(1 + y·z) = 1 + (1 + x·y)·z²   ⟺   x + y = z    (for z > 0)

is Tarski's identity as presented in Boolos, Burgess and Jeffrey, *Computability and Logic*,
Chapter 24. Expanding both sides leaves `x·z + y·z = z²`, which for `z > 0` is `x + y = z`.

## Scope

This is the *semantic* statement: an explicit formula over `ℕ`, proved to characterise addition.
It is deliberately not the model-theoretic statement `Definable₂` over a first-order language for
`(×, <)`, which would need `FirstOrder.Language` machinery that Mathlib does not yet exercise for
arithmetic beyond `ModelTheory/Arithmetic/Presburger`. What is proved here is the mathematical
content -- the formula exists and is correct; what is not proved is its packaging as a formula of
a formalised logic.
-/

namespace ZetaRigidity

/-! ## The successor, from the order alone -/

/-- The next formal product after `m` in the reconstructed magnitude order. -/
noncomputable def msucc (m : FormalProd) : FormalProd :=
  (exists_val_eq (n := val m + 1) (Nat.succ_pos _)).choose

@[simp] lemma val_msucc (m : FormalProd) : val (msucc m) = val m + 1 :=
  (exists_val_eq (n := val m + 1) (Nat.succ_pos _)).choose_spec

/-- **The successor is order-definable.** `msucc m` is characterised as the element above `m`
with nothing strictly between -- a condition in the language of the order alone. -/
theorem msucc_eq_iff (m n : FormalProd) :
    msucc m = n ↔ MLt m n ∧ ∀ r, ¬ (MLt m r ∧ MLt r n) := by
  simp only [MLt]
  constructor
  · rintro rfl
    refine ⟨by rw [val_msucc]; omega, fun r ⟨h1, h2⟩ => ?_⟩
    rw [val_msucc] at h2
    omega
  · rintro ⟨h1, h2⟩
    refine val_injective ?_
    rw [val_msucc]
    -- If the gap were more than one, the intermediate value would be attained.
    by_contra hne
    obtain ⟨r, hr⟩ := exists_val_eq (n := val m + 1) (Nat.succ_pos _)
    exact h2 r ⟨by omega, by omega⟩

/-! ## Robinson's identity -/

/-- **Tarski's identity**, over `ℕ`. For `z > 0` this characterises `x + y = z` using only
multiplication and `+ 1`. -/
theorem add_eq_iff_tarski {x y z : ℕ} (hz : 0 < z) :
    x + y = z ↔ (1 + x * z) * (1 + y * z) = 1 + (1 + x * y) * (z * z) := by
  constructor
  · rintro rfl; ring
  · intro h
    -- Expanding both sides cancels the `x·y·z²` terms and leaves `z·(x+y) = z·z`.
    have hcancel : z * (x + y) = z * z := by nlinarith [h]
    exact Nat.eq_of_mul_eq_mul_left hz hcancel

/-! ## Addition on the reconstructed structure -/

/-- **Addition is definable from multiplication and the order.** The right-hand side uses only
the monoid multiplication and `msucc`, and `msucc` is order-definable by `msucc_eq_iff`; so this
exhibits `+` inside the language `(×, <)`.

This is the precise form of the caveat recorded in `ZetaRigidity/Order.lean`: the ζ-condition
recovers the order, and the order brings addition back with it. The addition-free *appearance* of
`Twin` is a matter of notation, not of expressive power. -/
theorem add_definable (P Q R : FormalProd) :
    val R = val P + val Q ↔
      msucc (P * R) * msucc (Q * R) = msucc (msucc (P * Q) * R * R) := by
  have hR : 0 < val R := val_pos R
  rw [← val_injective.eq_iff]
  simp only [val_mul, val_msucc]
  rw [eq_comm (a := val R)]
  rw [add_eq_iff_tarski hR]
  constructor
  · intro h; linarith [h]
  · intro h; linarith [h]

/-- The contrapositive reading, stated plainly: the reconstructed structure is *not* an
addition-free arithmetic. Anything expressible with `+` is expressible without writing it. -/
theorem exists_add_definition :
    ∃ F : FormalProd → FormalProd → FormalProd → Prop,
      (∀ P Q R, F P Q R ↔ val R = val P + val Q) ∧
      (∀ P Q R, F P Q R ↔
        msucc (P * R) * msucc (Q * R) = msucc (msucc (P * Q) * R * R)) :=
  ⟨fun P Q R => val R = val P + val Q, fun _ _ _ => Iff.rfl, add_definable⟩

end ZetaRigidity

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings.MonoidAlgebra.Augmentation
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# A nonzero map for the trivial monoid

For `A = MonoidAlgebra Nat PUnit`, scalar multiplication on `Nat` is induced by
augmentation, while scalar multiplication on `A` is left multiplication. The map
`n ↦ single 1 n` is `A`-linear and does not vanish at `1`.
-/

local notation "A" => MonoidAlgebra Nat (PUnit : Type)

example :
    ∃ f : @LinearMap A A _ _ (RingHom.id A) Nat A _ _
      (MonoidAlgebra.augmentation Nat PUnit).toModule Semiring.toModule,
      f 1 ≠ 0 := by
  let _ : Module A Nat := (MonoidAlgebra.augmentation Nat PUnit).toModule
  let _ : Module A A := Semiring.toModule
  have hsingle (a : A) : a = MonoidAlgebra.single 1 (a.coeff 1) := by
    ext
    simp
  have hcollapse (a : A) :
      a = MonoidAlgebra.single 1 (MonoidAlgebra.augmentation Nat PUnit a) := by
    have ha : MonoidAlgebra.augmentation Nat PUnit a = a.coeff 1 := by
      calc
        MonoidAlgebra.augmentation Nat PUnit a =
            MonoidAlgebra.augmentation Nat PUnit (MonoidAlgebra.single 1 (a.coeff 1)) :=
          congrArg (MonoidAlgebra.augmentation Nat PUnit) (hsingle a)
        _ = a.coeff 1 := MonoidAlgebra.augmentation_single Nat PUnit 1 (a.coeff 1)
    rw [ha]
    exact hsingle a
  refine ⟨{
    toFun := fun n => MonoidAlgebra.single 1 n
    map_add' := by
      intro n m
      simp
    map_smul' := ?_
  }, ?_⟩
  · intro a n
    rw [RingHom.toModule_smul]
    change MonoidAlgebra.single 1 (MonoidAlgebra.augmentation Nat PUnit a * n) =
      a * MonoidAlgebra.single 1 n
    calc
      MonoidAlgebra.single 1 (MonoidAlgebra.augmentation Nat PUnit a * n) =
          MonoidAlgebra.single 1 (MonoidAlgebra.augmentation Nat PUnit a) *
            MonoidAlgebra.single 1 n := by
        simp only [MonoidAlgebra.single_mul_single, one_mul]
      _ = a * MonoidAlgebra.single 1 n := by rw [← hcollapse a]
  · change (MonoidAlgebra.single (1 : PUnit) (1 : Nat) : A) ≠ 0
    intro h
    have hcoeff := congrArg (fun a : A => a.coeff 1) h
    simp at hcoeff

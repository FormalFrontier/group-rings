/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Ordered ideal powers and augmentation nilpotence through the public import

The degree-zero bridge works for every semiring, without nontriviality or
subtraction. The infinite cyclic group cannot have nilpotent augmentation over
the noncommutative coefficient ring of two-by-two matrices over `ZMod 2`.
-/

private theorem zero_degree_iff (A : Type*) [Semiring A] (I : Ideal A) :
    I ^ 0 = ⊥ ↔ (1 : A) = 0 := by
  rw [Ideal.pow_eq_bot_iff_forall_list_prod_eq_zero]
  simp

private theorem infinite_cyclic_augmentation_not_nilpotent :
    ¬ IsNilpotent (RingHom.ker (MonoidAlgebra.augmentation
      (Matrix (Fin 2) (Fin 2) (ZMod 2)) (Multiplicative ℤ))) := by
  intro hI
  obtain ⟨k, hk⟩ := MonoidAlgebra.exists_pow_eq_one_of_isNilpotent_augmentation
    Nat.prime_two (CharP.cast_eq_zero (Matrix (Fin 2) (Fin 2) (ZMod 2)) 2) hI
  have h := congrArg Multiplicative.toAdd (hk (Multiplicative.ofAdd (1 : ℤ)))
  simp at h

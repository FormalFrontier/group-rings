/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Ordered ideal powers and augmentation nilpotence through the public import

The degree-zero bridge works for every semiring, without nontriviality or
subtraction. The infinite cyclic group cannot have nilpotent augmentation over
the noncommutative coefficient ring of two-by-two matrices over `ZMod 2`.
For the nonabelian dihedral group of order eight, the forward bound kills all
mixed products of length eight over that matrix ring. The zero coefficient
ring also satisfies the exact bound, although its characteristic is not two.
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

private theorem dihedral_matrix_mixed_products
    (l : List (MonoidAlgebra (Matrix (Fin 2) (Fin 2) (ZMod 2)) (DihedralGroup 4)))
    (hl : l.length = 8)
    (hmem : ∀ x ∈ l, x ∈ RingHom.ker (MonoidAlgebra.augmentation
      (Matrix (Fin 2) (Fin 2) (ZMod 2)) (DihedralGroup 4))) : l.prod = 0 := by
  have hG : IsPGroup 2 (DihedralGroup 4) :=
    IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; decide)
  exact MonoidAlgebra.augmentation_list_prod_eq_zero Nat.prime_two
    (CharP.cast_eq_zero (Matrix (Fin 2) (Fin 2) (ZMod 2)) 2) hG l
    (by simpa only [DihedralGroup.nat_card] using hl) hmem

private theorem dihedral_zero_ring_exact_bound :
    (RingHom.ker (MonoidAlgebra.augmentation (ZMod 1) (DihedralGroup 4))) ^ 8 = ⊥ := by
  have hG : IsPGroup 2 (DihedralGroup 4) :=
    IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; decide)
  simpa only [DihedralGroup.nat_card] using
    MonoidAlgebra.augmentation_pow_card_eq_bot (R := ZMod 1) Nat.prime_two
      (Subsingleton.elim _ _) hG

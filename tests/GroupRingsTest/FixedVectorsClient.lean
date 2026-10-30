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
# Common annihilators and fixed vectors through the public import

The ideal `(2)` acts nontrivially but with square zero on `ℤ/4ℤ`; it need not
vanish in the scalar ring. The fixed-vector theorem also applies to a module
of sequences over a nonabelian group algebra with matrix coefficients, with
no finiteness assumption on the module.
-/

private theorem two_common_annihilator_mod_four :
    (2 : ℤ) • (1 : ZMod 4) ≠ 0 ∧
      ∃ x : ZMod 4, x ≠ 0 ∧ (2 : ℤ) • x = 0 := by
  have : Fact (1 < 4) := ⟨by decide⟩
  refine ⟨by decide, ?_⟩
  have hpow : (Ideal.span ({2} : Set ℤ)) ^ 2 ≤ Module.annihilator ℤ (ZMod 4) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
      Module.mem_annihilator]
    intro x
    norm_num [zsmul_eq_mul]
    rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4, zero_mul]
  obtain ⟨x, hx, hI⟩ :=
    Ideal.exists_ne_zero_le_torsionOf_of_pow_le_annihilator _ hpow
  exact ⟨x, hx, (Ideal.mem_torsionOf_iff _ _).mp
    (hI (Ideal.subset_span (Set.mem_singleton 2)))⟩

private theorem dihedral_matrix_sequence_fixed :
    ∃ x : ℕ → MonoidAlgebra (Matrix (Fin 2) (Fin 2) (ZMod 2)) (DihedralGroup 4),
      x ≠ 0 ∧ ∀ g : DihedralGroup 4,
        MonoidAlgebra.single g (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) • x = x := by
  have hG : IsPGroup 2 (DihedralGroup 4) :=
    IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; decide)
  exact MonoidAlgebra.exists_ne_zero_fixed_of_isPGroup Nat.prime_two
    (CharP.cast_eq_zero (Matrix (Fin 2) (Fin 2) (ZMod 2)) 2) hG

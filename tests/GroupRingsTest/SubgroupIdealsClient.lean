/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.Perm.Finite

/-!
# A subgroup ideal which is not right-stable

The stabilizer of `2` in `S₃` is `{1, (01)}`. Over `M₂(ℤ)`, its basis
difference at `(01)` lies in the subgroup left ideal, but its right translate
by `(12)` does not. The obstruction is a nonzero coset coefficient, detected
through the public characteristic membership theorem.
-/

noncomputable section

namespace SubgroupIdeals

open MonoidAlgebra

private abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ
private abbrev S3 := Equiv.Perm (Fin 3)
private def tau : S3 := Equiv.swap 0 1
private def sigma : S3 := Equiv.swap 1 2
private def H : Subgroup S3 := MulAction.stabilizer S3 (2 : Fin 3)

private theorem matrix_noncomm :
    (Matrix.single 0 1 1 : M2) * Matrix.single 1 0 1 ≠
      (Matrix.single 1 0 1 : M2) * Matrix.single 0 1 1 := by decide

private theorem tau_mem : tau ∈ H := by
  change tau (2 : Fin 3) = 2
  decide

private theorem right_cosets_ne :
    QuotientGroup.mk (s := H) (tau * sigma) ≠ QuotientGroup.mk sigma := by
  intro h
  have hnot : (tau * sigma)⁻¹ * sigma ∉ H := by
    change ((tau * sigma)⁻¹ * sigma) (2 : Fin 3) ≠ 2
    decide
  exact hnot (QuotientGroup.eq.mp h)

private theorem right_projection_ne :
    cosetSum M2 H ((single tau 1 - 1) * single sigma 1) ≠ 0 := by
  classical
  intro h
  have hc := congrArg (fun f : S3 ⧸ H →₀ M2 => f (QuotientGroup.mk (tau * sigma))) h
  simp only [sub_mul, one_mul, single_mul_single, mul_one, map_sub, cosetSum_single,
    Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at hc
  rw [Finsupp.single_eq_of_ne right_cosets_ne, sub_zero] at hc
  exact one_ne_zero hc

private theorem generator_and_right_translate :
    single tau (1 : M2) - 1 ∈
        Ideal.span (Set.range (fun h : H => single (h : S3) (1 : M2) - 1)) ∧
      (single tau (1 : M2) - 1) * single sigma 1 ∉
        Ideal.span (Set.range (fun h : H => single (h : S3) (1 : M2) - 1)) := by
  refine ⟨(single_sub_one_mem_span_subgroup_iff M2 H tau).mpr tau_mem, ?_⟩
  exact fun hm => right_projection_ne ((mem_span_subgroup_iff M2 H _).mp hm)

/-- Arbitrary left multiplication need not be coefficient-linear, even after
projection; the two coefficient factors cannot be interchanged. -/
private theorem projected_left_mul_not_linear :
    cosetSum M2 H (single (1 : S3) (Matrix.single 0 1 1) *
        ((Matrix.single 1 0 1 : M2) • single 1 (1 : M2))) ≠
      (Matrix.single 1 0 1 : M2) •
        cosetSum M2 H (single (1 : S3) (Matrix.single 0 1 1) * single 1 (1 : M2)) := by
  intro h
  have hc := congrArg (fun f : S3 ⧸ H →₀ M2 => f (QuotientGroup.mk (1 : S3))) h
  exact matrix_noncomm (by simpa using hc)

end SubgroupIdeals

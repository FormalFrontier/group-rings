/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Data.Matrix.Basic

/-!
The coefficient ring here is the noncommutative ring of two-by-two integer
matrices. The index homomorphism is the inclusion of integer units into the
multiplicative monoid of integers, whose image is proper. These clients use the
quotient and factorization APIs without a group structure on the target.
-/

open MonoidAlgebra

local notation "A" => Matrix (Fin 2) (Fin 2) ℤ

private theorem integer_units_not_surjective :
    ¬ Function.Surjective (Units.coeHom ℤ) := by
  intro h
  obtain ⟨u, hu⟩ := h 0
  exact u.ne_zero hu

private theorem matrix_unit_range_class (g : ℤˣ) (r : A) :
    (quotientSpanKerEquivMrange A (Units.coeHom ℤ)).symm
      (single ((Units.coeHom ℤ).mrangeRestrict g) r) =
      Ideal.Quotient.mk _ (single g r) := by
  apply (quotientSpanKerEquivMrange A (Units.coeHom ℤ)).injective
  rw [RingEquiv.apply_symm_apply, quotientSpanKerEquivMrange_mk_single]

private theorem matrix_unit_range_augmentation :
    ∃ ψ : MonoidAlgebra A (MonoidHom.mrange (Units.coeHom ℤ)) →+* A,
      ψ.comp (mapDomainRingHom A (Units.coeHom ℤ).mrangeRestrict) =
        augmentation A ℤˣ ∧
      ∀ (g : ℤˣ) (r : A),
        ψ (single ((Units.coeHom ℤ).mrangeRestrict g) r) = r := by
  obtain ⟨ψ, hψ, _⟩ :=
    (existsUnique_comp_mapDomainRingHom_mrangeRestrict_iff A (Units.coeHom ℤ)
      (augmentation A ℤˣ)).mpr (by intro n; simp [augmentation_single])
  refine ⟨ψ, hψ, ?_⟩
  intro g r
  simpa only [augmentation_single] using
    comp_mapDomainRingHom_single A (Units.coeHom ℤ).mrangeRestrict
      (augmentation A ℤˣ) ψ hψ g r

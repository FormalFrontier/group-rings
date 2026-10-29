/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import GroupRings.RingTheory.Ideal.MonoidHom

/-!
# Augmentation ideals from monoid and group generators

For any ring of coefficients, differences `single s 1 - 1` for a generating
set of the monoid generate the augmentation kernel as a left ideal. For a
group, generation as an ordinary subgroup suffices; generation as a monoid
is not required. Neither coefficient commutativity nor finiteness is assumed.

The proofs restrict the generators of `MonoidAlgebra.ker_augmentation` using
the difference-membership lemmas for arbitrary left ideals.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

/-- A monoid generating set supplies left-ideal generators of the augmentation kernel. -/
theorem ker_augmentation_eq_span_of_submonoid_closure_eq_top
    (R : Type u) [Ring R] (M : Type v) [Monoid M]
    (S : Set M) (hS : Submonoid.closure S = ⊤) :
    RingHom.ker (augmentation R M) =
      Ideal.span ((fun s : M => single s (1 : R) - 1) '' S) := by
  rw [ker_augmentation]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    apply Ideal.sub_one_mem_of_mem_submonoid_closure
      (Ideal.span ((fun s : M => single s (1 : R) - 1) '' S)) (of R M)
    · intro s hs
      exact Ideal.subset_span ⟨s, hs, rfl⟩
    · rw [hS]
      exact Submonoid.mem_top m
  · exact Ideal.span_mono (Set.image_subset_range _ _)

/-- A subgroup generating set supplies left-ideal generators of the augmentation kernel. -/
theorem ker_augmentation_eq_span_of_subgroup_closure_eq_top
    (R : Type u) [Ring R] (G : Type v) [Group G]
    (S : Set G) (hS : Subgroup.closure S = ⊤) :
    RingHom.ker (augmentation R G) =
      Ideal.span ((fun s : G => single s (1 : R) - 1) '' S) := by
  rw [ker_augmentation]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    apply Ideal.sub_one_mem_of_mem_subgroup_closure
      (Ideal.span ((fun s : G => single s (1 : R) - 1) '' S)) (of R G)
    · intro s hs
      exact Ideal.subset_span ⟨s, hs, rfl⟩
    · rw [hS]
      exact Subgroup.mem_top g
  · exact Ideal.span_mono (Set.image_subset_range _ _)

end MonoidAlgebra

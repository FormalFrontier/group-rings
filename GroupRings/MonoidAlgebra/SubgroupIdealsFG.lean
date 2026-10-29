/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationGenerators
public import GroupRings.MonoidAlgebra.SubgroupIdeals
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation of subgroup augmentation ideals

The left ideal spanned by the differences `single h 1 - 1` for a finitely
generated subgroup is finitely generated over the group ring. Over a nontrivial
coefficient ring, the converse holds as well. Specializing to the whole group
characterizes finite generation of the augmentation kernel.

Coefficients need not commute, and subgroups need not be normal. The forward
implications also hold over the zero ring. Finite generation here is as a left
ideal over the group ring, not as a module over the coefficient ring.

The proofs use Mathlib's finite-subset characterization of finitely generated
spans, together with subgroup closure of left-ideal differences and reflection
of subgroup inclusion by their left ideals.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

/-- A finitely generated subgroup gives a finitely generated left ideal over any ring. -/
theorem span_subgroup_fg_of_fg
    (R : Type u) [Ring R] {G : Type v} [Group G]
    (H : Subgroup G) (hH : H.FG) :
    (Ideal.span (Set.range (fun h : H => single (h : G) (1 : R) - 1)) :
      Ideal (MonoidAlgebra R G)).FG := by
  obtain ⟨S, hS, hfin⟩ := (Subgroup.fg_iff H).mp hH
  have heq :
      Ideal.span (Set.range (fun h : H => single (h : G) (1 : R) - 1)) =
        Ideal.span ((fun s : G => single s (1 : R) - 1) '' S) := by
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      apply Ideal.sub_one_mem_of_mem_subgroup_closure
        (Ideal.span ((fun s : G => single s (1 : R) - 1) '' S)) (of R G)
      · intro s hs
        exact Ideal.subset_span ⟨s, hs, rfl⟩
      · rw [hS]
        exact h.property
    · apply Ideal.span_mono
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨s, hS ▸ Subgroup.subset_closure hs⟩, rfl⟩
  rw [heq]
  exact Submodule.fg_span (hfin.image _)

/-- Over a nontrivial ring, finite generation of the subgroup left ideal detects
finite generation of the subgroup. -/
theorem span_subgroup_fg_iff
    (R : Type u) [Ring R] [Nontrivial R] {G : Type v} [Group G]
    (H : Subgroup G) :
    (Ideal.span (Set.range (fun h : H => single (h : G) (1 : R) - 1)) :
      Ideal (MonoidAlgebra R G)).FG ↔ H.FG := by
  classical
  refine ⟨fun hI => ?_, span_subgroup_fg_of_fg R H⟩
  obtain ⟨t, ht, heq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := MonoidAlgebra R G)
      (Set.range (fun h : H => single (h : G) (1 : R) - 1))).mp hI
  change Ideal.span (Set.range (fun h : H => single (h : G) (1 : R) - 1)) =
    Ideal.span (t : Set (MonoidAlgebra R G)) at heq
  -- Choose subgroup labels for the finite subset of the original differences.
  choose f hf using fun z : t => ht z.property
  let S : Set G := Set.range (fun z : t => (f z : G))
  have hSH : Subgroup.closure S ≤ H := by
    refine (Subgroup.closure_le H).mpr ?_
    rintro _ ⟨z, rfl⟩
    exact (f z).property
  have hHS : H ≤ Subgroup.closure S := by
    apply (span_subgroup_le_iff R H (Subgroup.closure S)).mp
    rw [heq]
    refine Ideal.span_le.mpr ?_
    intro z hz
    have hz' : single (f ⟨z, hz⟩ : G) (1 : R) - 1 = z := hf ⟨z, hz⟩
    rw [← hz']
    exact Ideal.subset_span ⟨⟨(f ⟨z, hz⟩ : G), Subgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩⟩, rfl⟩
  exact (Subgroup.fg_iff H).mpr ⟨S, le_antisymm hSH hHS, Set.finite_range _⟩

private theorem span_subgroup_top
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Ideal.span (Set.range (fun h : (⊤ : Subgroup G) => single (h : G) (1 : R) - 1)) =
      RingHom.ker (augmentation R G) := by
  rw [ker_augmentation]
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(g : G), rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩

/-- The augmentation kernel is a finitely generated left ideal for a finitely
generated group over any coefficient ring. -/
theorem ker_augmentation_fg
    (R : Type u) [Ring R] (G : Type v) [Group G] [Group.FG G] :
    (RingHom.ker (augmentation R G)).FG := by
  rw [← span_subgroup_top]
  exact span_subgroup_fg_of_fg R ⊤ Group.FG.out

/-- Over a nontrivial coefficient ring, the augmentation kernel is finitely
generated as a left ideal exactly when the group is finitely generated. -/
theorem ker_augmentation_fg_iff
    (R : Type u) [Ring R] [Nontrivial R] (G : Type v) [Group G] :
    (RingHom.ker (augmentation R G)).FG ↔ Group.FG G := by
  rw [← span_subgroup_top, span_subgroup_fg_iff, Group.fg_def]

end MonoidAlgebra

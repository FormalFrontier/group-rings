/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Left ideals finite over the coefficients

If `R` and `S` are semirings and `S` is an `R`-module, a finitely generated
`R`-submodule of `S[M]` has a common finite bound on the supports of all its
elements. This support bound does not require any monoid structure on the index type.

For a monoid algebra over a semiring, a nonzero left ideal finite over the
coefficient semiring forces a cancellative monoid to be finite: left
multiplication moves a fixed nonzero coefficient to every point of an injective
monoid orbit inside that bound.

The coefficients may be any semiring, including a noncommutative or zero one.
The ideal is finite over the coefficients, not merely over the monoid algebra.
This is not a criterion for the monoid algebra itself to be Artinian.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

variable {R : Type u} {M : Type v} [Semiring R]

/-- The elements of a finitely generated submodule of `S[M]` have uniformly
bounded support, even when the index type has no monoid structure. -/
theorem exists_finset_support_subset_of_fg {S : Type w} [Semiring S] [Module R S]
    (N : Submodule R (MonoidAlgebra S M)) (hN : N.FG) :
    ∃ s : Finset M, ∀ f ∈ N, f.coeff.support ⊆ s := by
  classical
  obtain ⟨t, ht⟩ := hN
  let s := t.biUnion fun f => f.coeff.support
  refine ⟨s, ?_⟩
  have hle : N ≤ supported R S (s : Set M) := by
    rw [← ht]
    refine Submodule.span_le.mpr ?_
    intro f hf
    apply MonoidAlgebra.mem_supported.mpr
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨f, hf, hm⟩
  intro f hf
  exact hle hf

/-- A nonzero left ideal finite as a coefficient module forces a cancellative
monoid to be finite. There is no commutativity or nontriviality assumption on
the coefficient semiring, and the coefficient and monoid universes are independent. -/
theorem finite_of_moduleFinite_ideal [CancelMonoid M]
    (I : Ideal (MonoidAlgebra R M)) (hI : I ≠ ⊥)
    [Module.Finite R (I.restrictScalars R)] : Finite M := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_support_subset_of_fg (I.restrictScalars R)
    (Submodule.FG.of_finite (N := I.restrictScalars R))
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hfc : f.coeff ≠ 0 := fun h => hf0 (MonoidAlgebra.coeff_eq_zero.mp h)
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hfc
  have hmem (m : M) : m * a ∈ s := by
    apply hs (single m 1 * f) (I.mul_mem_left (single m 1) hf)
    rw [support_coeff_single_mul_eq_image f (r := 1) (by simp) (.all m)]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  exact Finite.of_injective (fun m : M => (⟨m * a, hmem m⟩ : s)) (by
    intro m n h
    exact mul_right_cancel (congrArg Subtype.val h))

end MonoidAlgebra

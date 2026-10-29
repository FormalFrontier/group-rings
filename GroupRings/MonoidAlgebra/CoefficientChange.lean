/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation

/-!
# Augmentation ideals under coefficient change

Augmentation commutes with any unital homomorphism of semirings. Its kernel
pulls back to the preimage of the coefficient kernel. When the source
coefficients form a ring, the image ideal is the entire target augmentation
kernel, without requiring the coefficient homomorphism to be surjective.
The reverse inclusion uses left multiples of the images of
`single m 1 + single 1 (-1)`, so no target negation is needed.
-/

@[expose] public section

namespace MonoidAlgebra

universe u v w

variable {R : Type u} {S : Type v} {M : Type w}
section Semiring

variable [Semiring R] [Semiring S] [Monoid M]

/-- Augmentation commutes with coefficient change as a ring homomorphism. -/
theorem augmentation_comp_mapRingHom (φ : R →+* S) :
    (augmentation S M).comp (mapRingHom M φ) =
      φ.comp (augmentation R M) := by
  apply ringHom_ext <;> intro x <;>
    simp only [RingHom.comp_apply, mapRingHom_single, augmentation_single, map_one]

/-- Coefficient change commutes with the sum of coefficients. -/
@[simp] theorem augmentation_mapRingHom (φ : R →+* S) (x : R[M]) :
    augmentation S M (mapRingHom M φ x) = φ (augmentation R M x) :=
  DFunLike.congr_fun (augmentation_comp_mapRingHom (M := M) φ) x

/-- The preimage of the target augmentation kernel detects the coefficient kernel. -/
theorem comap_ker_augmentation_mapRingHom (φ : R →+* S) :
    Ideal.comap (mapRingHom M φ) (RingHom.ker (augmentation S M)) =
      Ideal.comap (augmentation R M) (RingHom.ker φ) := by
  ext x
  simp only [Ideal.mem_comap, RingHom.mem_ker, augmentation_mapRingHom]

end Semiring

section Ring

variable [Ring R] [Semiring S] [Monoid M]

/-- Coefficient change maps the source augmentation ideal onto the target
augmentation ideal. Surjectivity of the coefficient homomorphism is not needed. -/
theorem map_ker_augmentation_mapRingHom (φ : R →+* S) :
    Ideal.map (mapRingHom M φ) (RingHom.ker (augmentation R M)) =
      RingHom.ker (augmentation S M) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    apply Ideal.mem_comap.mpr
    apply RingHom.mem_ker.mpr
    rw [augmentation_mapRingHom, RingHom.mem_ker.mp hx, map_zero]
  · intro x hx
    have h : x + single (1 : M) (augmentation S M x * φ (-1)) ∈
        Ideal.map (mapRingHom M φ) (RingHom.ker (augmentation R M)) := by
      clear hx
      induction x using induction_linear with
      | zero => simp
      | add x y hx hy =>
        simpa only [map_add, add_mul, single_add, add_assoc, add_left_comm, add_comm]
          using Ideal.add_mem _ hx hy
      | single m s =>
        have hg : single m (1 : R) + single (1 : M) (-1 : R) ∈
            RingHom.ker (augmentation R M) := by
          simp only [RingHom.mem_ker, map_add, augmentation_single, add_neg_cancel]
        have hm := Ideal.mul_mem_left
          (Ideal.map (mapRingHom M φ) (RingHom.ker (augmentation R M)))
          (single (1 : M) s) (Ideal.mem_map_of_mem (mapRingHom M φ) hg)
        simpa only [augmentation_single, map_add, mapRingHom_single, map_one,
          mul_add, single_mul_single, one_mul, mul_one] using hm
    simpa only [RingHom.mem_ker.mp hx, zero_mul, single_zero, add_zero] using h

end Ring

end MonoidAlgebra

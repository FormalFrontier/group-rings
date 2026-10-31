/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import GroupRings.RingTheory.Artinian

/-!
# Coefficient change in monoid algebras

An additive retraction of a coefficient homomorphism extends coefficientwise
using Mathlib's `MonoidAlgebra.map`. Compatibility with right multiplication
by the coefficient image extends to the monoid algebras. Consequently, left
Artinianity descends along such a coefficient homomorphism. The coefficients
may be noncommutative or zero, and the monoid is arbitrary.

The bundled additive map used for Artinian descent is the composite of
Mathlib's coefficient additive equivalences and `Finsupp.mapRange.addMonoidHom`;
no new coefficient-map construction is needed.

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

/-- A coefficientwise additive left inverse retracts coefficient change. -/
theorem map_mapRingHom_of_leftInverse (φ : R →+* S) (E : S →+ R)
    (hE : ∀ r, E (φ r) = r) (x : MonoidAlgebra R M) :
    map E (mapRingHom M φ x) = x := by
  ext m
  simpa using hE (x.coeff m)

/-- A coefficient map compatible with right multiplication by a coefficient
image is compatible with right multiplication by the entire monoid-algebra image. -/
theorem map_mul_mapRingHom (φ : R →+* S) (E : S →+ R)
    (hmul : ∀ s r, E (s * φ r) = E s * r)
    (x : MonoidAlgebra S M) (y : MonoidAlgebra R M) :
    map E (x * mapRingHom M φ y) = map E x * y := by
  induction x using induction_linear with
  | zero => simp
  | add x z hx hz =>
    simp only [add_mul, MonoidAlgebra.map_add, hx, hz]
  | single m s =>
    induction y using induction_linear with
    | zero => simp
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.map_add, hy, hz]
    | single n r => simp [single_mul_single, hmul]

/-- Left Artinianity of a monoid algebra descends along a coefficient
homomorphism with an additive retraction compatible with right multiplication
by the coefficient image. No Artinian restriction-of-scalars assumption is needed. -/
theorem isArtinianRing_of_coefficient_additive_retraction
    (φ : R →+* S) (E : S →+ R)
    (hE : ∀ r, E (φ r) = r)
    (hmul : ∀ s r, E (s * φ r) = E s * r)
    [IsArtinianRing (MonoidAlgebra S M)] : IsArtinianRing (MonoidAlgebra R M) := by
  let E' : MonoidAlgebra S M →+ MonoidAlgebra R M :=
    coeffAddEquiv.symm.toAddMonoidHom.comp
      ((Finsupp.mapRange.addMonoidHom E).comp coeffAddEquiv.toAddMonoidHom)
  have hE'_apply (x : MonoidAlgebra S M) : E' x = map E x := rfl
  apply (mapRingHom M φ).isArtinianRing_of_additive_retraction E'
  · intro x
    simpa only [hE'_apply] using map_mapRingHom_of_leftInverse φ E hE x
  · intro x y
    simpa only [hE'_apply] using map_mul_mapRingHom φ E hmul x y

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

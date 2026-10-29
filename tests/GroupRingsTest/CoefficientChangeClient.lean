/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-!
# Coefficient change through the public group-ring API
-/

open MonoidAlgebra

universe u v w
variable {R : Type u} {S : Type v} {M : Type w}

section Semiring
variable [Semiring R] [Semiring S] [Monoid M]

theorem coefficientChange_mem_augmentationKernel (φ : R →+* S) (x : R[M])
    (hx : augmentation R M x ∈ RingHom.ker φ) :
    mapRingHom M φ x ∈ RingHom.ker (augmentation S M) := by
  apply Ideal.mem_comap.mp
  rw [comap_ker_augmentation_mapRingHom]
  exact Ideal.mem_comap.mpr hx

end Semiring

section Ring
variable [Ring R] [Semiring S] [Monoid M]

theorem augmentationZero_mem_coefficientImage (φ : R →+* S) (x : S[M])
    (hx : augmentation S M x = 0) :
    x ∈ Ideal.map (mapRingHom M φ) (RingHom.ker (augmentation R M)) := by
  rw [map_ker_augmentation_mapRingHom]
  exact RingHom.mem_ker.mpr hx

end Ring

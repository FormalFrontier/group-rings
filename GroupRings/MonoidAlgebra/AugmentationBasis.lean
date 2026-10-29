/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.LinearAlgebra.Finsupp.SumKernel
public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# A coefficient-module basis of the augmentation kernel

For any ring `R` and monoid `M`, the augmentation kernel has a basis over `R`
indexed by `{m : M // m ≠ 1}`. Its vectors are `single m 1 - 1`, and its
coordinates are the coefficients away from the identity. Scalars act on the
left through the coefficients; this is not a basis over `MonoidAlgebra R M`.

The semiring-level bridges identify the sum of the coordinates in Mathlib's
monoid-algebra basis with the coefficient-sum augmentation, and identify its
restricted kernel with the kernel of the linear coefficient sum. The
basis then uses `Finsupp.kerLsumEquiv` and Mathlib's `Module.Basis.ofRepr`.

## Implementation notes

No commutativity, group, cancellation, finiteness, nontriviality or decidable
equality hypothesis is required. The zero ring and singleton monoids are
allowed. Subtraction requires ring coefficients for the basis, but the
supporting coefficient-sum bridges need only a semiring.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

variable (R : Type u) (M : Type v)

section Semiring

variable [Semiring R] [Monoid M]

/-- Summing the coordinates in the monoid-algebra basis is augmentation. -/
theorem sumCoords_basis_apply (x : MonoidAlgebra R M) :
    (basis M R).sumCoords x = augmentation R M x :=
  (augmentation_apply R M x).symm

/-- Restricting the augmentation kernel to coefficient scalars gives the kernel
of the linear coefficient sum composed with the coefficient equivalence. -/
theorem ker_augmentation_restrictScalars :
    (RingHom.ker (augmentation R M)).restrictScalars R =
      LinearMap.ker ((Finsupp.lsum ℕ (fun _ : M => (LinearMap.id : R →ₗ[R] R))).comp
        (coeffLinearEquiv R).toLinearMap) := by
  ext x
  change augmentation R M x = 0 ↔ x.coeff.sum (fun _ r => r) = 0
  rw [augmentation_apply]

end Semiring

section Ring

variable [Ring R] [Monoid M]

/-- The left coefficient-`R`-module basis of the augmentation kernel, with vector
`single m 1 - 1` at each nonidentity index `m`. Coordinates are the coefficients
away from the identity. -/
def augmentationKerBasis : Module.Basis {m : M // m ≠ 1} R
    ((RingHom.ker (augmentation R M)).restrictScalars R) :=
  Module.Basis.ofRepr <|
    (LinearEquiv.ofEq _ _ (ker_augmentation_restrictScalars R M)).trans <|
      ((coeffLinearEquiv R).ofSubmodule'
        (LinearMap.ker (Finsupp.lsum ℕ (fun _ : M => (LinearMap.id : R →ₗ[R] R))))).trans
        (Finsupp.kerLsumEquiv R R (1 : M))

/-- A basis vector in the augmentation kernel is the corresponding basis
monomial minus the identity. -/
@[simp]
theorem coe_augmentationKerBasis (m : {m : M // m ≠ 1}) :
    (augmentationKerBasis R M m : MonoidAlgebra R M) = single m.val 1 - 1 := by
  change (coeffLinearEquiv R).symm
    (((Finsupp.kerLsumEquiv R R (1 : M)).symm (Finsupp.single m 1) : M →₀ R)) = _
  rw [Finsupp.kerLsumEquiv_symm_apply_coe]
  simp only [Finsupp.mapDomain_single, Finsupp.sum_single_index]
  change ofCoeff (Finsupp.single m.val 1 - Finsupp.single (1 : M) 1) = _
  simp [one_def]

/-- The coordinates of a kernel element are its coefficients at nonidentity indices. -/
@[simp]
theorem augmentationKerBasis_repr_apply
    (x : (RingHom.ker (augmentation R M)).restrictScalars R) (m : {m : M // m ≠ 1}) :
    (augmentationKerBasis R M).repr x m = (x : MonoidAlgebra R M).coeff m.val := rfl

end Ring

end MonoidAlgebra

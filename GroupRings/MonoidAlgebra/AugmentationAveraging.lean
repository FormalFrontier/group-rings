/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCrossedUniversal
public import GroupTheory.CocycleAveraging
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Averaging crossed maps on a group-algebra module

If the order of a finite group is a unit in the coefficient ring, every crossed
map for the given group-algebra action is principal. Its witness is the negative
inverse-order multiple of the sum. Linear maps from the full augmentation ideal
are consequently induced by the action on a vector. No commutativity or
nontriviality assumption is needed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

universe uR uG uV uW
namespace MonoidAlgebra
variable (R : Type uR) (G : Type uG) [Ring R] [Group G]
variable (V : Type uV) [AddCommGroup V] [Module R[G] V]

/-- The negative inverse-order multiple of the sum is a principal witness. -/
theorem augmentationCocycles_eq_smul_sub_average [Fintype G]
    (hR : IsUnit (Nat.card G : R)) (z : augmentationCocycles R G V) (g : G) :
    z g = (single g 1 : R[G]) •
        (-Function.invFun (fun v : V => Nat.card G • v) (∑ h, z h)) -
      (-Function.invFun (fun v : V => Nat.card G • v) (∑ h, z h)) := by
  let : Module R V := moduleCoefficientModule R G V
  let : DistribMulAction G V := moduleMonoidAction R G V
  have hN : Function.Bijective (fun v : V => Nat.card G • v) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hR.smul_bijective (β := V)
  have hact (h : G) (v : V) : h • v = (single h 1 : R[G]) • v :=
    moduleMonoidAction_apply R G V h v
  have hz : groupCohomology.IsCocycle₁ (fun h => z h) := by
    intro h k
    simpa only [hact, add_comm] using
      augmentationCocycles_map_mul R G V z h k
  have hi : Function.invFun (fun v : V => Nat.card G • v) =
      (Equiv.ofBijective _ hN).symm :=
    Function.invFun_eq_of_injective_of_rightInverse hN.1
      (Equiv.ofBijective _ hN).apply_symm_apply
  rw [hi]
  simpa only [hact] using
    hz.eq_smul_sub_inverse_nsmul_sum hN g

/-- Crossed maps for the given action are principal when the order is a unit. -/
theorem augmentationCocycles_exists_eq_smul_sub [Finite G]
    (hR : IsUnit (Nat.card G : R)) (z : augmentationCocycles R G V) :
    ∃ v : V, ∀ g : G, z g = (single g 1 : R[G]) • v - v := by
  let := Fintype.ofFinite G
  exact ⟨-Function.invFun (fun v : V => Nat.card G • v) (∑ h, z h),
    augmentationCocycles_eq_smul_sub_average R G V hR z⟩

/-- Averaging commutes with every additive map, hence with coefficient-module
maps and group-algebra linear maps. -/
theorem augmentationCocycles_average_natural [Fintype G]
    (W : Type uW) [AddCommGroup W] [Module R[G] W]
    (hR : IsUnit (Nat.card G : R)) (f : V →+ W) (z : augmentationCocycles R G V) :
    f (-Function.invFun (fun v : V => Nat.card G • v) (∑ g, z g)) =
      -Function.invFun (fun w : W => Nat.card G • w) (∑ g, f (z g)) := by
  let : Module R V := moduleCoefficientModule R G V
  let : Module R W := moduleCoefficientModule R G W
  have hV : Function.Bijective (fun v : V => Nat.card G • v) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hR.smul_bijective (β := V)
  have hW : Function.Bijective (fun w : W => Nat.card G • w) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hR.smul_bijective (β := W)
  have eV : Function.invFun (fun v : V => Nat.card G • v) =
      (Equiv.ofBijective _ hV).symm :=
    Function.invFun_eq_of_injective_of_rightInverse hV.1
      (Equiv.ofBijective _ hV).apply_symm_apply
  have eW : Function.invFun (fun w : W => Nat.card G • w) =
      (Equiv.ofBijective _ hW).symm :=
    Function.invFun_eq_of_injective_of_rightInverse hW.1
      (Equiv.ofBijective _ hW).apply_symm_apply
  rw [eV, eW]
  exact f.map_neg_inverse_nsmul_sum (Nat.card G) hV hW (fun g => z g)

/-- Every group-algebra linear map out of the full augmentation ideal is induced
by the action on a vector when the group order is a unit. -/
theorem augmentationIdealAction_surjective_of_isUnit [Finite G]
    (hR : IsUnit (Nat.card G : R)) :
    Function.Surjective (augmentationIdealAction R G V) := by
  intro F
  obtain ⟨v, hv⟩ := augmentationCocycles_exists_eq_smul_sub R G V hR
    (augmentationCrossedEquiv R G V F)
  refine ⟨v, ?_⟩
  apply (augmentationCrossedEquiv R G V).injective
  apply augmentationCocycles_ext R G V
  intro g
  simpa only [augmentationCrossedEquiv_principal] using (hv g).symm

end MonoidAlgebra

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCotangent.Universal

/-!
# The augmentation cotangent module of a group

For any (possibly noncommutative) unital ring `R` and group `G`, the augmentation
cotangent module is `R ⊗[ℤ] Additive (Abelianization G)`, as a left `R`-module.
This generalizes the classical integral augmentation-ideal/abelianization
comparison. Brown's *Cohomology of Groups* is a reference for the classical
integral background, not the source of the proof used here. The construction
uses the monoid-character universal property, group abelianization and the
integer tensor product; no freeness assumption is required.

## References

* Kenneth S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics,
  Springer, 1982. https://doi.org/10.1007/978-1-4684-9327-6
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe u v
namespace MonoidAlgebra
variable (R : Type u) (G : Type v) [Ring R] [Group G]

/-- Send a basis-difference class to the corresponding pure abelianization tensor. -/
def augmentationCotangentToTensor :
    AugmentationCotangent R G →ₗ[R] R ⊗[ℤ] Additive (Abelianization G) :=
  augmentationCotangentLift R G
    { toFun g := Multiplicative.ofAdd
        (1 ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g))
      map_one' := by
        change (1 : R) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of (1 : G)) = 0
        simp
      map_mul' g h := by
        change (1 : R) ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of (g * h)) =
          1 ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g) +
            1 ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of h)
        simp only [map_mul, ofMul_mul, TensorProduct.tmul_add] }

@[simp]
theorem augmentationCotangentToTensor_delta (g : G) :
    augmentationCotangentToTensor R G (augmentationCotangentDelta R G g) =
      1 ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g) :=
  augmentationCotangentLift_delta R G _ g

/-- Send a pure abelianization tensor to its coefficient-weighted cotangent class. -/
def augmentationCotangentFromTensor :
    R ⊗[ℤ] Additive (Abelianization G) →ₗ[R] AugmentationCotangent R G :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton R _
      (MonoidHom.toAdditiveLeft
        (Abelianization.lift (augmentationCotangentDeltaHom R G))).toIntLinearMap)

@[simp]
theorem augmentationCotangentFromTensor_tmul (r : R) (g : G) :
    augmentationCotangentFromTensor R G
      (r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g)) =
      r • augmentationCotangentDelta R G g := by
  simp only [augmentationCotangentFromTensor, TensorProduct.AlgebraTensorModule.lift_tmul]
  change r • (Abelianization.lift (augmentationCotangentDeltaHom R G)
    (Abelianization.of g)).toAdd = _
  rw [Abelianization.lift_apply_of]
  rfl

private theorem augmentationCotangentFromTensor_toTensor :
    (augmentationCotangentFromTensor R G).comp (augmentationCotangentToTensor R G) =
      LinearMap.id := by
  apply augmentationCotangent_linearMap_ext R G
  intro g
  simp

private theorem augmentationCotangentToTensor_fromTensor :
    (augmentationCotangentToTensor R G).comp (augmentationCotangentFromTensor R G) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r b =>
    obtain ⟨g, hg⟩ := Quot.exists_rep b.toMul
    rw [Abelianization.mk_eq_of] at hg
    have hb : Additive.ofMul (Abelianization.of g) = b := congrArg Additive.ofMul hg
    rw [← hb]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The augmentation cotangent module of a group algebra is the integer tensor of
its additive abelianization, as a left `R`-module.

For `R = ℤ`, this recovers the classical integral augmentation-ideal/abelianization
comparison; see Kenneth S. Brown, *Cohomology of Groups* (1982), for classical
background. Here the coefficient ring may be noncommutative, and neither the
group nor its abelianization is assumed free.
The proof uses the monoid-character universal property followed by the universal
properties of abelianization and the integer tensor product; it does not follow
a proof from Brown. -/
def augmentationCotangentTensorEquiv :
    AugmentationCotangent R G ≃ₗ[R] R ⊗[ℤ] Additive (Abelianization G) :=
  LinearEquiv.ofLinearMap (augmentationCotangentToTensor R G)
    (augmentationCotangentFromTensor R G)
    (by exact augmentationCotangentToTensor_fromTensor R G)
    (by exact augmentationCotangentFromTensor_toTensor R G)

@[simp]
theorem augmentationCotangentTensorEquiv_delta (g : G) :
    augmentationCotangentTensorEquiv R G (augmentationCotangentDelta R G g) =
      1 ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g) :=
  augmentationCotangentToTensor_delta R G g

@[simp]
theorem augmentationCotangentTensorEquiv_symm_tmul (r : R) (g : G) :
    (augmentationCotangentTensorEquiv R G).symm
      (r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g)) =
      r • augmentationCotangentDelta R G g :=
  augmentationCotangentFromTensor_tmul R G r g

end MonoidAlgebra

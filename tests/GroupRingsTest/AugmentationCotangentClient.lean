/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings

/-! The two universal descriptions together characterize extension from abelianization tensors. -/

open MonoidAlgebra
open scoped TensorProduct

universe u v w

private theorem existsUnique_abelianizationTensor_extension (R : Type u) (G : Type v) (V : Type w)
    [Ring R] [Group G] [AddCommGroup V] [Module R V]
    (h : G →* Multiplicative V) :
    ∃! F : R ⊗[ℤ] Additive (Abelianization G) →ₗ[R] V,
      ∀ (r : R) (g : G),
        F (r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g)) = r • (h g).toAdd := by
  let E := augmentationCotangentTensorEquiv R G
  let f := (augmentationCotangentEquiv R G).symm h
  let F := f.comp E.symm.toLinearMap
  refine ⟨F, ?_, ?_⟩
  · intro r g
    change f (E.symm (r ⊗ₜ[ℤ] Additive.ofMul (Abelianization.of g))) = _
    rw [augmentationCotangentTensorEquiv_symm_tmul, map_smul]
    exact congrArg (fun v => r • v) (augmentationCotangentEquiv_symm_delta R G h g)
  · intro K hK
    have hk : K.comp E.toLinearMap = f := by
      apply augmentationCotangent_linearMap_ext R G
      intro g
      change K (E (augmentationCotangentDelta R G g)) =
        f (augmentationCotangentDelta R G g)
      rw [augmentationCotangentTensorEquiv_delta]
      simpa only [f, one_smul, augmentationCotangentEquiv_symm_delta] using hK 1 g
    apply LinearMap.ext
    intro t
    have ht := LinearMap.congr_fun hk (E.symm t)
    simpa only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using ht

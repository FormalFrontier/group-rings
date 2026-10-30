/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupRings
import Mathlib.Algebra.Field.ZMod

/-!
# Simple-module applications through the public import

The regular module of a nontrivial finite `p`-group algebra in characteristic
`p` is not simple: triviality of its group action would identify distinct
basis elements. Conversely, the augmentation pullback of the prime field
is simple. These use the regular action and the augmentation action,
respectively, rather than inferring trivial action from one fixed vector.
-/

universe u v

private theorem regular_not_simple
    {R : Type u} [Ring R] [Nontrivial R] {G : Type v} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G)
    {g : G} (hg : g ≠ 1) :
    ¬ IsSimpleModule (MonoidAlgebra R G) (MonoidAlgebra R G) := by
  intro h
  let := h
  have heq := MonoidAlgebra.single_smul_eq_of_isSimpleModule_of_isPGroup
    hp hR hG g (1 : MonoidAlgebra R G)
  have heq' : MonoidAlgebra.single g (1 : R) = 1 := by
    simpa only [smul_eq_mul, mul_one] using heq
  have hc := congrArg (fun a : MonoidAlgebra R G => a.coeff g) heq'
  simp [MonoidAlgebra.one_def, hg] at hc

section PrimeField

variable (M : Type v) [Monoid M]

private noncomputable instance primeFieldAction : Module (MonoidAlgebra (ZMod 2) M) (ZMod 2) :=
  Module.compHom (ZMod 2) (MonoidAlgebra.augmentation (ZMod 2) M)

private theorem primeField_simple :
    IsSimpleModule (MonoidAlgebra (ZMod 2) M) (ZMod 2) := by
  let : RingHomSurjective (MonoidAlgebra.augmentation (ZMod 2) M) :=
    ⟨MonoidAlgebra.augmentation_surjective (ZMod 2) M⟩
  let f : ZMod 2 →ₛₗ[MonoidAlgebra.augmentation (ZMod 2) M] ZMod 2 :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (f.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

end PrimeField

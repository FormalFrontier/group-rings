/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Commuting quotient scalar actions

For an ideal-annihilated module, `Module.IsTorsionBySet.hasSMul` gives the scalar action of
the additive quotient of the ring. This action commutes with every action commuting with
the original ring action. Consequently, two commuting ring actions remain commuting after
both scalar rings are replaced by quotients by annihilating ideals.

For two-sided ideals these are the quotient-ring module actions supplied by
`Module.IsTorsionBySet.module`. Compatible base-scalar towers are already supplied by
`Module.IsTorsionBySet.isScalarTower`.
-/

@[expose] public section

namespace Module

universe u v w

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-- The quotient scalar action of an ideal-annihilated module commutes with any action
commuting with the original ring action. The other scalars need only an action. -/
theorem IsTorsionBySet.smulCommClass (hM : IsTorsionBySet R M I)
    (S : Type w) [SMul S M] [SMulCommClass R S M] :
    @SMulCommClass (R ⧸ I) S M hM.hasSMul _ := by
  let _ := hM.hasSMul
  refine ⟨fun q s m => ?_⟩
  exact Quotient.inductionOn' q fun r => smul_comm r s m

/-- Two commuting ring actions still commute after quotienting both scalar rings by
ideals annihilating the module. Two-sidedness is needed only to obtain quotient rings,
not for commutativity of these quotient scalar actions. -/
theorem IsTorsionBySet.smulCommClass_quotient
    {S : Type w} [Ring S] [Module S M] [SMulCommClass R S M]
    {J : Ideal S} (hR : IsTorsionBySet R M I) (hS : IsTorsionBySet S M J) :
    @SMulCommClass (R ⧸ I) (S ⧸ J) M hR.hasSMul hS.hasSMul := by
  let _ := hR.hasSMul
  let _ := hS.hasSMul
  let _ : SMulCommClass (R ⧸ I) S M := hR.smulCommClass S
  let _ : SMulCommClass S (R ⧸ I) M := SMulCommClass.symm _ _ _
  let _ : SMulCommClass (S ⧸ J) (R ⧸ I) M := hS.smulCommClass (R ⧸ I)
  exact SMulCommClass.symm _ _ _

end Module

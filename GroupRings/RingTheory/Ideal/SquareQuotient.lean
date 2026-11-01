/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Module.QuotientActions
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actions on an ideal modulo its square

For a two-sided ideal `I` of an arbitrary ring `A`, the quotient
`I ⧸ Submodule.comap I.subtype (I ^ 2)` has its usual left action and the right action induced by
multiplication in `A`. These actions commute, and each is annihilated by `I`.
Noetherianity on the right is inherited from the right regular module of `A`;
Noetherianity on the left is already inherited by Mathlib's submodule and quotient instances.

The carrier is the ordinary submodule quotient, without a wrapper. The right action is
obtained by descending right multiplication through its stable additive relation, not
from a scalar tower between the left and right regular actions. Compatible base scalars
retain their existing action on the quotient.

The equality `smul_top_eq_comap_sq` compares this presentation with Mathlib's commutative
`Ideal.Cotangent` presentation.
-/

@[expose] public section

universe u v

namespace Ideal

variable {A : Type u} [Ring A] (I : Ideal A)

/-- The ideal-action presentation of the square relation equals the ordinary-square
comap presentation, without any commutativity assumption. -/
theorem smul_top_eq_comap_sq :
    I • (⊤ : Submodule A I) = Submodule.comap I.subtype (I ^ 2) := by
  ext x
  change x ∈ I • (⊤ : Submodule A I) ↔ (x : A) ∈ I ^ 2
  rw [Submodule.pow_succ, Submodule.pow_one]
  simpa only [Ideal.smul_eq_mul] using
    (Submodule.mem_smul_top_iff (I := I) I x)

/-- A class in the ideal-square quotient vanishes exactly when its representative lies
in the ordinary ideal square. -/
theorem mk_squareQuotient_eq_zero (x : I) :
    (Submodule.Quotient.mk x : I ⧸ Submodule.comap I.subtype (I ^ 2)) = 0 ↔
      (x : A) ∈ I ^ 2 :=
  Submodule.Quotient.mk_eq_zero _

/-- Left multiplication on representatives of the ideal-square quotient. -/
theorem smul_mk_squareQuotient (a : A) (x : I) :
    a • (Submodule.Quotient.mk x : I ⧸ Submodule.comap I.subtype (I ^ 2)) =
      Submodule.Quotient.mk ⟨a * (x : A), I.mul_mem_left a x.property⟩ :=
  rfl

/-- The ideal annihilates its quotient by its square on the left. -/
theorem isTorsionBySet_squareQuotient :
    Module.IsTorsionBySet A (I ⧸ Submodule.comap I.subtype (I ^ 2)) I := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x a ha
  change a * (x : A) ∈ I ^ 2
  rw [Submodule.pow_succ, Submodule.pow_one]
  exact Ideal.mul_mem_mul ha x.property

section Right

variable [I.IsTwoSided]

/-- Right multiplication makes the original two-sided ideal subtype a right module. -/
instance moduleMulOpposite : Module Aᵐᵒᵖ I :=
  let J : Submodule Aᵐᵒᵖ A :=
    { toAddSubmonoid := I.toAddSubmonoid
      smul_mem' a _ hx := I.mul_mem_right a.unop hx }
  inferInstanceAs (Module Aᵐᵒᵖ J)

instance smulCommClass_mulOpposite : SMulCommClass A Aᵐᵒᵖ I where
  smul_comm a b x := Subtype.ext (smul_comm a b (x : A))

/-- Right multiplication preserves the ordinary square relation. -/
instance squareQuotientSMulMulOpposite :
    SMul Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) where
  smul a := Quotient.map' (a • ·) fun x y h => by
    apply (Submodule.quotientRel_def (Submodule.comap I.subtype (I ^ 2))).2
    change (x : A) * a.unop - (y : A) * a.unop ∈ I ^ 2
    rw [← sub_mul]
    exact (I ^ 2).mul_mem_right a.unop
      ((Submodule.quotientRel_def (Submodule.comap I.subtype (I ^ 2))).1 h)

/-- The canonical right module on the ordinary ideal-square quotient. -/
instance squareQuotientModuleMulOpposite :
    Module Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  Function.Surjective.module Aᵐᵒᵖ
    (Submodule.comap I.subtype (I ^ 2)).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (fun _ _ => rfl)

/-- Right multiplication on representatives of the ideal-square quotient. -/
theorem op_smul_mk_squareQuotient (a : A) (x : I) :
    MulOpposite.op a • (Submodule.Quotient.mk x : I ⧸ Submodule.comap I.subtype (I ^ 2)) =
      Submodule.Quotient.mk ⟨(x : A) * a, I.mul_mem_right a x.property⟩ :=
  rfl

instance squareQuotientSMulCommClass :
    SMulCommClass A Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) where
  smul_comm a b q := by
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      exact congrArg (Submodule.Quotient.mk (p := Submodule.comap I.subtype (I ^ 2)))
        (smul_comm a b x)

/-- Right Noetherianity of the ideal follows from that of the right regular module. -/
instance isNoetherian_mulOpposite [IsNoetherianRing Aᵐᵒᵖ] : IsNoetherian Aᵐᵒᵖ I := by
  let f : I →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (x : A)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact isNoetherian_of_injective f (MulOpposite.op_injective.comp Subtype.coe_injective)

/-- Right Noetherianity passes to the ideal-square quotient using its right-linear
quotient map. No comparison of opposite ideal powers is needed. -/
instance isNoetherian_squareQuotient_mulOpposite [IsNoetherian Aᵐᵒᵖ I] :
    IsNoetherian Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) := by
  let f : I →ₗ[Aᵐᵒᵖ] (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact isNoetherian_of_surjective f
    (LinearMap.range_eq_top.mpr (Submodule.Quotient.mk_surjective _))

/-- The left quotient-ring action is induced by the original left action. -/
instance squareQuotientModuleQuotient :
    Module (A ⧸ I) (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  (isTorsionBySet_squareQuotient I).module

/-- The quotient-ring scalar action agrees with the original left scalar action. -/
@[simp]
theorem quotient_mk_smul_squareQuotient (a : A) (q : I ⧸ Submodule.comap I.subtype (I ^ 2)) :
    Ideal.Quotient.mk I a • q = a • q :=
  (isTorsionBySet_squareQuotient I).mk_smul a q

instance squareQuotientQuotientSMulCommClass :
    SMulCommClass (A ⧸ I) Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  (isTorsionBySet_squareQuotient I).smulCommClass Aᵐᵒᵖ

/-- Noetherianity for the descended left action follows from the original left action. -/
instance isNoetherian_squareQuotient_quotient [IsNoetherian A I] :
    IsNoetherian (A ⧸ I) (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  ((isTorsionBySet_squareQuotient I).semilinearMap.isNoetherian_iff_of_bijective
    Function.bijective_id).mp inferInstance

/-- The kernel of the opposite quotient map annihilates the right action. -/
theorem isTorsionBySet_squareQuotient_mulOpposite :
    Module.IsTorsionBySet Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2))
      (RingHom.ker (Ideal.Quotient.mk I).op) := by
  intro q a
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    change (Submodule.Quotient.mk (a.val • x) :
      I ⧸ Submodule.comap I.subtype (I ^ 2)) = 0
    rw [mk_squareQuotient_eq_zero]
    change (x : A) * a.val.unop ∈ I ^ 2
    rw [Submodule.pow_succ, Submodule.pow_one]
    exact Ideal.mul_mem_mul x.property
      (Ideal.Quotient.eq_zero_iff_mem.mp (MulOpposite.op_injective a.property))

private theorem quotient_op_surjective : Function.Surjective (Ideal.Quotient.mk I).op := by
  intro q
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective q.unop
  exact ⟨MulOpposite.op a, congrArg MulOpposite.op ha⟩

/-- The canonical right quotient-ring action, descended from the original right action
through the opposite of the quotient map. -/
noncomputable instance squareQuotientModuleQuotientMulOpposite :
    Module (A ⧸ I)ᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) := by
  letI := (isTorsionBySet_squareQuotient_mulOpposite I).module
  have hf : Function.Surjective (Ideal.Quotient.mk I).op := by
    intro q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective q.unop
    exact ⟨MulOpposite.op a, congrArg MulOpposite.op ha⟩
  exact Module.compHom _
    ((Ideal.Quotient.mk I).op.quotientKerEquivOfSurjective hf).symm.toRingHom

/-- The descended right action agrees with the original right action. -/
@[simp]
theorem op_quotient_mk_smul_squareQuotient (a : A)
    (q : I ⧸ Submodule.comap I.subtype (I ^ 2)) :
    MulOpposite.op (Ideal.Quotient.mk I a) • q = MulOpposite.op a • q := by
  let := (isTorsionBySet_squareQuotient_mulOpposite I).module
  change ((Ideal.Quotient.mk I).op.quotientKerEquivOfSurjective
    (quotient_op_surjective I)).symm ((Ideal.Quotient.mk I).op (MulOpposite.op a)) • q = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

instance squareQuotientSMulCommClass_quotientMulOpposite :
    SMulCommClass A (A ⧸ I)ᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) where
  smul_comm a b q := by
    obtain ⟨b', hb⟩ := Ideal.Quotient.mk_surjective b.unop
    have hb' : MulOpposite.op (Ideal.Quotient.mk I b') = b :=
      congrArg MulOpposite.op hb
    rw [← hb']
    simp only [op_quotient_mk_smul_squareQuotient]
    exact smul_comm a (MulOpposite.op b') q

/-- Both quotient-ring actions commute on the original ideal-square quotient. -/
instance squareQuotientQuotientSMulCommClass_quotientMulOpposite :
    SMulCommClass (A ⧸ I) (A ⧸ I)ᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  (isTorsionBySet_squareQuotient I).smulCommClass (A ⧸ I)ᵐᵒᵖ

/-- A composed left/right quotient scalar action vanishes exactly when the ordinary
sandwich product belongs to the ideal square. -/
theorem quotient_smul_op_quotient_smul_mk_squareQuotient_eq_zero_iff
    (a b : A) (x : I) :
    Ideal.Quotient.mk I a •
        (MulOpposite.op (Ideal.Quotient.mk I b) •
          (Submodule.Quotient.mk x : I ⧸ Submodule.comap I.subtype (I ^ 2))) = 0 ↔
      a * (x : A) * b ∈ I ^ 2 := by
  rw [quotient_mk_smul_squareQuotient, op_quotient_mk_smul_squareQuotient,
    op_smul_mk_squareQuotient, smul_mk_squareQuotient, mk_squareQuotient_eq_zero,
    mul_assoc]

/-- Right Noetherianity is retained when the scalars descend to the opposite quotient
ring. -/
instance isNoetherian_squareQuotient_quotientMulOpposite
    [IsNoetherian Aᵐᵒᵖ I] :
    IsNoetherian (A ⧸ I)ᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) := by
  let : RingHomSurjective (Ideal.Quotient.mk I).op := ⟨quotient_op_surjective I⟩
  let f : (I ⧸ Submodule.comap I.subtype (I ^ 2)) →ₛₗ[(Ideal.Quotient.mk I).op]
      I ⧸ Submodule.comap I.subtype (I ^ 2) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a q => (op_quotient_mk_smul_squareQuotient I a.unop q).symm }
  exact isNoetherian_of_surjective f (LinearMap.range_eq_top.mpr Function.surjective_id)

end Right

section Base

variable {S : Type v} [CommSemiring S] [Algebra S A] [I.IsTwoSided]

/-- Compatible base scalars and right multiplication retain their tower on the
original ideal subtype. -/
instance isScalarTower_mulOpposite : IsScalarTower S Aᵐᵒᵖ I where
  smul_assoc s a x := Subtype.ext (smul_assoc s a (x : A))

/-- Compatible base scalars and right multiplication retain their original tower on
the ideal-square quotient. -/
instance squareQuotientIsScalarTower_mulOpposite :
    IsScalarTower S Aᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) where
  smul_assoc s a q := by
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      exact congrArg (Submodule.Quotient.mk (p := Submodule.comap I.subtype (I ^ 2)))
        (smul_assoc s a x)

/-- The original base action remains compatible with the descended left action. -/
instance squareQuotientIsScalarTower_quotient :
    IsScalarTower S (A ⧸ I) (I ⧸ Submodule.comap I.subtype (I ^ 2)) :=
  (isTorsionBySet_squareQuotient I).isScalarTower

/-- Compatible base scalars retain their tower after descending the right action. -/
instance squareQuotientIsScalarTower_quotientMulOpposite :
    IsScalarTower S (A ⧸ I)ᵐᵒᵖ (I ⧸ Submodule.comap I.subtype (I ^ 2)) where
  smul_assoc s a q := by
    obtain ⟨a', ha⟩ := Ideal.Quotient.mk_surjective a.unop
    have ha' : MulOpposite.op (Ideal.Quotient.mk I a') = a :=
      congrArg MulOpposite.op ha
    rw [← ha']
    change MulOpposite.op (Ideal.Quotient.mk I (s • a')) • q =
      s • (MulOpposite.op (Ideal.Quotient.mk I a') • q)
    simp only [op_quotient_mk_smul_squareQuotient]
    exact smul_assoc s (MulOpposite.op a') q

/-- The left and right actions of a base scalar on the first ideal-square quotient
are both its original base action. -/
theorem algebraMap_op_smul_squareQuotient (s : S)
    (q : I ⧸ Submodule.comap I.subtype (I ^ 2)) :
    MulOpposite.op (algebraMap S (A ⧸ I) s) • q = s • q := by
  change MulOpposite.op (Ideal.Quotient.mk I (algebraMap S A s)) • q = _
  rw [op_quotient_mk_smul_squareQuotient]
  rw [← MulOpposite.algebraMap_apply]
  exact algebraMap_smul Aᵐᵒᵖ s q

end Base

section CommRing

variable {B : Type u} [CommRing B] (J : Ideal B)

/-- In the commutative case the canonical right action agrees with the existing left
action on the same quotient carrier. -/
theorem op_smul_squareQuotient (a : B) (q : J ⧸ Submodule.comap J.subtype (J ^ 2)) :
    MulOpposite.op a • q = a • q := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    rw [op_smul_mk_squareQuotient, smul_mk_squareQuotient]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (mul_comm (x : B) a))

/-- The square-comap relation gives the same vanishing test as Mathlib's cotangent
projection. -/
theorem mk_squareQuotient_eq_zero_iff_toCotangent_eq_zero (x : J) :
    (Submodule.Quotient.mk x : J ⧸ Submodule.comap J.subtype (J ^ 2)) = 0 ↔
      J.toCotangent x = 0 := by
  rw [mk_squareQuotient_eq_zero, Ideal.toCotangent_eq_zero]

end CommRing

end Ideal

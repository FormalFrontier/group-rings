/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# A subgroup basis for a group algebra

For a semiring `R`, a group `G` and a subgroup `H`, the group algebra `R[G]`
is free as a left `R[H]`-module. The index is the quotient by
`QuotientGroup.rightRel H`: these are the right cosets `H * g`, which are
preserved by left multiplication by `H`.

`MonoidAlgebra.basisSubgroup` uses the representative `q.out` of each
right coset. Its coordinate at `q` is `MonoidAlgebra.subgroupCoord H q`,
whose coefficient at `h : H` is the coefficient at `h * q.out` in the original
algebra. `MonoidAlgebra.subgroupRepr` packages these coordinates as a finitely
supported linear equivalence, and its inverse reconstructs an element by
left-ordered multiplication of the coordinates by the basis vectors.

The scalar action throughout is restriction of the regular left action along
`MonoidAlgebra.mapDomainRingHom R H.subtype`. No commutativity, normality or
nontriviality assumption is required. Finite index gives a finite module;
no numerical rank assertion is made.

The construction uses Mathlib's coefficient equivalence and the domain and
currying equivalences for finitely supported functions.
-/

@[expose] public section

noncomputable section

namespace MonoidAlgebra

universe u v

variable {R : Type u} [Semiring R] {G : Type v} [Group G]

private theorem rightCoset_mk_mul_out (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (h : H) :
    Quotient.mk (QuotientGroup.rightRel H) ((h : G) * q.out) = q := by
  refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)
  apply QuotientGroup.rightRel_apply.mpr
  simp

/-- Multiplication identifies a right coset together with a subgroup coordinate
with a group element. The representative is chosen internally. -/
private def rightCosetMulEquiv (H : Subgroup G) :
    (Quotient (QuotientGroup.rightRel H) × H) ≃ G :=
  Equiv.ofBijective (fun p => (p.2 : G) * p.1.out) <| by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ he
      have hq : q = q' := by
        simpa only [rightCoset_mk_mul_out] using
          congrArg (Quotient.mk (QuotientGroup.rightRel H)) he
      subst q'
      have hh : h = h' := Subtype.ext (mul_right_cancel he)
      subst h'
      rfl
    · intro g
      let q : Quotient (QuotientGroup.rightRel H) := Quotient.mk _ g
      have hm : g * q.out⁻¹ ∈ H :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq q))
      exact ⟨(q, ⟨g * q.out⁻¹, hm⟩), by simp⟩

private theorem rightCosetMulEquiv_apply (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (h : H) :
    rightCosetMulEquiv H (q, h) = (h : G) * q.out := rfl

private def subgroupReprAddEquiv (H : Subgroup G) :
    MonoidAlgebra R G ≃+
      (Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) :=
  coeffAddEquiv.trans <|
    (Finsupp.domCongr (rightCosetMulEquiv H).symm).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv coeffAddEquiv.symm

private theorem subgroupReprAddEquiv_coeff (H : Subgroup G)
    (f : MonoidAlgebra R G) (q : Quotient (QuotientGroup.rightRel H)) (h : H) :
    ((subgroupReprAddEquiv H f q).coeff h) = f.coeff ((h : G) * q.out) := by
  simp [subgroupReprAddEquiv, Finsupp.domCongr, rightCosetMulEquiv_apply]

private theorem subgroupReprAddEquiv_single (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (h : H) (r : R) :
    subgroupReprAddEquiv H (single ((h : G) * q.out) r) =
      Finsupp.single q (single h r) := by
  have he : (rightCosetMulEquiv H).symm ((h : G) * q.out) = (q, h) :=
    (rightCosetMulEquiv H).symm_apply_apply (q, h)
  simp [subgroupReprAddEquiv, Finsupp.domCongr, he, Finsupp.curry_single]

private theorem subgroupReprAddEquiv_symm_single (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (h : H) (r : R) :
    (subgroupReprAddEquiv H).symm (Finsupp.single q (single h r)) =
      single ((h : G) * q.out) r := by
  apply (subgroupReprAddEquiv H).injective
  simpa using (subgroupReprAddEquiv_single H q h r).symm

private theorem subgroupReprAddEquiv_symm_eq (H : Subgroup G)
    (c : Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    (subgroupReprAddEquiv H).symm c =
      Finsupp.linearCombination (MonoidAlgebra R H)
        (fun q : Quotient (QuotientGroup.rightRel H) => single q.out (1 : R)) c := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single q a =>
      obtain ⟨a, rfl⟩ := (coeffAddEquiv (R := R) (M := H)).symm.surjective a
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, Finsupp.single_add, ha, hb]
      | single h r =>
          change (subgroupReprAddEquiv H).symm (Finsupp.single q (single h r)) = _
          rw [subgroupReprAddEquiv_symm_single, Finsupp.linearCombination_single]
          change single ((h : G) * q.out) r =
            mapDomainRingHom R H.subtype (single h r) * single q.out 1
          simp [mapDomainRingHom]

/-- The coordinate of a group algebra element on the right coset `q`.
Its coefficient at `h : H` is the original coefficient at `h * q.out`. -/
def subgroupCoord (H : Subgroup G) (q : Quotient (QuotientGroup.rightRel H))
    (f : MonoidAlgebra R G) : MonoidAlgebra R H :=
  comapDomain (fun h : H => (h : G) * q.out)
    ((mul_left_injective q.out).comp Subtype.val_injective) f

@[simp]
theorem subgroupCoord_coeff (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (f : MonoidAlgebra R G) (h : H) :
    (subgroupCoord H q f).coeff h = f.coeff ((h : G) * q.out) := by
  simp [subgroupCoord]

@[simp]
theorem subgroupCoord_zero (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    subgroupCoord (R := R) H q 0 = 0 := by
  ext h
  simp

@[simp]
theorem subgroupCoord_add (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (f g : MonoidAlgebra R G) :
    subgroupCoord H q (f + g) = subgroupCoord H q f + subgroupCoord H q g := by
  ext h
  simp

/-- The finitely supported right-coset coordinates of a group algebra, linear
for the left subgroup-algebra action obtained by `Module.compHom`. -/
def subgroupRepr (H : Subgroup G) :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    MonoidAlgebra R G ≃ₗ[MonoidAlgebra R H]
      (Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) := by
  letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  let e : (Quotient (QuotientGroup.rightRel H) × H) ≃ G :=
    Equiv.ofBijective (fun p => (p.2 : G) * p.1.out)
      (by exact (rightCosetMulEquiv H).bijective)
  let E : MonoidAlgebra R G ≃+
      (Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) :=
    coeffAddEquiv.trans <| (Finsupp.domCongr e.symm).trans <|
      Finsupp.curryAddEquiv.trans <| Finsupp.mapRange.addEquiv coeffAddEquiv.symm
  exact (show (Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) ≃ₗ[
    MonoidAlgebra R H] MonoidAlgebra R G from
    { __ := E.symm
      map_smul' := by
        intro a c
        change (subgroupReprAddEquiv H).symm (a • c) =
          a • (subgroupReprAddEquiv H).symm c
        simp only [subgroupReprAddEquiv_symm_eq, map_smul] }).symm

@[simp]
theorem subgroupRepr_apply (H : Subgroup G) (f : MonoidAlgebra R G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    subgroupRepr H f q = subgroupCoord H q f := by
  ext h
  exact (subgroupReprAddEquiv_coeff H f q h).trans (subgroupCoord_coeff H q f h).symm

theorem subgroupRepr_coeff (H : Subgroup G) (f : MonoidAlgebra R G)
    (q : Quotient (QuotientGroup.rightRel H)) (h : H) :
    (subgroupRepr H f q).coeff h = f.coeff ((h : G) * q.out) := by simp

/-- Coordinates reconstruct by multiplying each subgroup coefficient on the
left of its chosen coset vector. -/
theorem subgroupRepr_symm_apply (H : Subgroup G)
    (c : Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) :
    (subgroupRepr H).symm c =
      c.sum (fun q a => mapDomainRingHom R H.subtype a * single q.out 1) := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  rw [show (subgroupRepr H).symm c = (subgroupReprAddEquiv H).symm c from rfl,
    subgroupReprAddEquiv_symm_eq, Finsupp.linearCombination_apply]
  rfl

/-- The right-coset basis of the group algebra as a left subgroup-algebra module. -/
def basisSubgroup (H : Subgroup G) :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    Module.Basis (Quotient (QuotientGroup.rightRel H))
      (MonoidAlgebra R H) (MonoidAlgebra R G) := by
  letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  exact Module.Basis.ofRepr (subgroupRepr H)

@[simp]
theorem basisSubgroup_apply (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    basisSubgroup (R := R) H q = single q.out 1 := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  change (subgroupReprAddEquiv (R := R) H).symm (Finsupp.single q 1) = _
  simpa [one_def] using subgroupReprAddEquiv_symm_single (R := R) H q 1 1

@[simp]
theorem basisSubgroup_repr (H : Subgroup G) :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    (basisSubgroup (R := R) H).repr = subgroupRepr H := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  rfl

/-- Coordinate extraction commutes with multiplication on the left by the
subgroup algebra, with coefficient order unchanged. -/
@[simp]
theorem subgroupCoord_mapDomain_mul (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H))
    (a : MonoidAlgebra R H) (f : MonoidAlgebra R G) :
    subgroupCoord H q (mapDomain (Subtype.val : H → G) a * f) =
      a * subgroupCoord H q f := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  have he := congrArg (fun c => c q) ((subgroupRepr H).map_smul a f)
  have hs : a • f = mapDomainRingHom R H.subtype a * f := rfl
  simpa only [hs, subgroupRepr_apply, Finsupp.smul_apply, smul_eq_mul,
    mapDomainRingHom_apply, Subgroup.coe_subtype] using he

/-- Reconstructing all right-coset coordinates recovers the original element. -/
theorem subgroupCoord_sum (H : Subgroup G) (f : MonoidAlgebra R G) :
    (subgroupRepr H f).sum
      (fun q a => mapDomainRingHom R H.subtype a * single q.out 1) = f := by
  rw [← subgroupRepr_symm_apply, LinearEquiv.symm_apply_apply]

/-- Taking right-coset coordinates after reconstruction recovers the prescribed
finitely supported family. -/
@[simp]
theorem subgroupRepr_sum (H : Subgroup G)
    (c : Quotient (QuotientGroup.rightRel H) →₀ MonoidAlgebra R H) :
    subgroupRepr H
      (c.sum (fun q a => mapDomain (Subtype.val : H → G) a * single q.out 1)) = c := by
  have he := (subgroupRepr H).apply_symm_apply c
  rw [subgroupRepr_symm_apply] at he
  simpa only [mapDomainRingHom_apply, Subgroup.coe_subtype] using he

/-- A finite-index subgroup algebra makes the group algebra a finite left module,
even when the coefficient semiring is zero or noncommutative. -/
theorem finite_subgroup (H : Subgroup G) [H.FiniteIndex] :
    letI := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
    Module.Finite (MonoidAlgebra R H) (MonoidAlgebra R G) := by
  let := Module.compHom (MonoidAlgebra R G) (mapDomainRingHom R H.subtype)
  let : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Module.Finite.of_basis (basisSubgroup H)

end MonoidAlgebra

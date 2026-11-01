/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import GroupRings.RingTheory.IdempotentCentrality
import GroupRings.RingTheory.Ideal.ScalarRestriction
import GroupRings.RingTheory.Ideal.SquareQuotient
import GroupRings.RingTheory.Module.ScalarRestriction
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Abel

/-!
# Central summands finite over the base ring

For an algebra `A` over a commutative ring `R` that is Artinian on both sides,
every `R`-algebra character `χ : A →ₐ[R] R` is one on a central idempotent whose
principal left ideal is finitely generated over `R`.

The ideal carries the scalar action inherited from the given algebra structure.
The base ring need not be a field or reduced. The character is surjective, so
Artinianity of the base ring follows from the hypotheses. The whole algebra need
not be finite over `R`, and the idempotent need not be primitive.

## Proof strategy

The greatest finite-base left ideal in the semisimple Jacobson quotient is
two-sided and centrally idempotent-generated. Its support acts identically on
every compatible base-Noetherian representation. Applied on both sides of the
first radical layer, this makes the two support operators agree. An idempotent
lift is then central, and nilpotent ideal-action finiteness measures its left
ideal. The character is compared in `R ⧸ Ring.jacobson R`, rather than in `R`.
-/

@[expose] public section

universe u v

namespace AlgHom

private theorem eq_zero_of_sandwich_eq_zero {S : Type*} [Ring S]
    [IsSemisimpleRing S] {x : S} (hx : ∀ y : S, x * y * x = 0) : x = 0 := by
  have hxJ : x ∈ Ideal.jacobson (⊥ : Ideal S) := by
    refine Ideal.mem_jacobson_iff.mpr fun y ↦ ⟨1 - y * x, ?_⟩
    have hsq : y * x * y * x = 0 := by
      calc
        y * x * y * x = y * (x * y * x) := by simp only [mul_assoc]
        _ = 0 := by rw [hx y, mul_zero]
    have hz : (1 - y * x) * y * x + (1 - y * x) - 1 = 0 := by
      simp only [sub_mul, one_mul, hsq, sub_zero]
      abel
    simpa only [hz] using (⊥ : Ideal S).zero_mem
  rw [Ideal.jacobson_bot, IsSemisimpleRing.jacobson_eq_bot] at hxJ
  exact hxJ

private theorem exists_central_idempotent_generator {S : Type*} [Ring S]
    [IsSemisimpleRing S] (I : Ideal S) [I.IsTwoSided] :
    ∃ e : S, IsIdempotentElem e ∧ IsMulCentral e ∧ I = Ideal.span {e} := by
  obtain ⟨e, he, hIe⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have hfix : ∀ x ∈ I, x * e = x := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (hIe ▸ hx)
    simp only [mul_assoc, he.eq]
  have heI : e ∈ I := hIe.symm ▸ Ideal.mem_span_singleton_self e
  have hdiag (a : S) : e * a * e = e * a := hfix _ (I.mul_mem_right a heI)
  have hcross (a : S) : e * a * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hdiag, sub_self]
  refine ⟨e, he, ⟨fun a ↦ ?_, fun _ _ ↦ (mul_assoc _ _ _).symm,
    fun _ _ ↦ mul_assoc _ _ _⟩, hIe⟩
  have hzero : (1 - e) * a * e = 0 := by
    apply eq_zero_of_sandwich_eq_zero
    intro b
    calc
      (1 - e) * a * e * b * ((1 - e) * a * e) =
          (1 - e) * a * (e * b * (1 - e)) * a * e := by simp only [mul_assoc]
      _ = 0 := by rw [hcross, mul_zero, zero_mul, zero_mul]
  have h : a * e - e * a = 0 := by
    simpa only [sub_mul, one_mul, hdiag] using hzero
  exact (sub_eq_zero.mp h).symm

private theorem exists_maximal_finite_support (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] [IsSemisimpleRing S] :
    ∃ p : S, IsIdempotentElem p ∧ IsMulCentral p ∧
      Module.Finite R (Ideal.span ({p} : Set S)) ∧
      ∀ I : Ideal S, Module.Finite R I → I ≤ Ideal.span ({p} : Set S) := by
  obtain ⟨I, hI, htwo⟩ := Ideal.exists_isGreatest_finite R S
  let : I.IsTwoSided := htwo
  obtain ⟨p, hp, hpc, hIp⟩ := exists_central_idempotent_generator I
  refine ⟨p, hp, hpc, hIp ▸ hI.1, ?_⟩
  intro N hN
  exact (hI.2 hN).trans_eq hIp

private theorem mem_span_idempotent_iff {S : Type*} [Ring S] {e x : S}
    (he : IsIdempotentElem e) : x ∈ Ideal.span ({e} : Set S) ↔ x * e = x := by
  constructor
  · rintro hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp only [mul_assoc, he.eq]
  · intro hx
    exact Ideal.mem_span_singleton'.mpr ⟨x, hx⟩

private theorem central_one_sub {S : Type*} [Ring S] {e : S}
    (hc : IsMulCentral e) : IsMulCentral (1 - e) := by
  refine ⟨fun a ↦ ?_, fun _ _ ↦ (mul_assoc _ _ _).symm,
    fun _ _ ↦ mul_assoc _ _ _⟩
  change (1 - e) * a = a * (1 - e)
  simpa only [sub_mul, mul_sub, one_mul, mul_one] using
    congrArg (fun x : S ↦ a - x) (hc.comm a).eq

private theorem exists_finite_support (R : Type*) {S : Type*} {M : Type*}
    [CommRing R] [Ring S] [Algebra R S] [IsSemisimpleRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [IsNoetherian R M] :
    ∃ e : S, IsIdempotentElem e ∧ IsMulCentral e ∧
      Module.Finite R (Ideal.span ({e} : Set S)) ∧ ∀ m : M, e • m = m := by
  obtain ⟨f, hf, hfc, hIf⟩ :=
    exists_central_idempotent_generator (Module.annihilator S M)
  have hfI : f ∈ Module.annihilator S M :=
    hIf.symm ▸ Ideal.mem_span_singleton_self f
  let P : Ideal S := Ideal.span {1 - f}
  let ρ : S →ₐ[R] Module.End R M := Algebra.lsmul R R M
  let j : P →ₗ[R] Module.End R M := ρ.toLinearMap.comp (P.subtype.restrictScalars R)
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    apply Subtype.ext
    have hxI : (x : S) ∈ Module.annihilator S M := by
      apply Module.mem_annihilator.mpr
      intro m
      exact DFunLike.congr_fun hx m
    have hxf : (x : S) * f = x :=
      (mem_span_idempotent_iff hf).mp (hIf ▸ hxI)
    have hxe : (x : S) * (1 - f) = x :=
      (mem_span_idempotent_iff hf.one_sub).mp x.property
    rw [mul_sub, mul_one, hxf, sub_self] at hxe
    exact hxe.symm
  let : IsNoetherian R P := isNoetherian_of_injective j hj
  refine ⟨1 - f, hf.one_sub, central_one_sub hfc, inferInstance, fun m ↦ ?_⟩
  rw [sub_smul, one_smul, Module.mem_annihilator.mp hfI m, sub_zero]

private theorem support_eq_one (R : Type*) {S : Type*} {M : Type*}
    [CommRing R] [Ring S] [Algebra R S] [IsSemisimpleRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [IsNoetherian R M] {p : S} (hp : IsIdempotentElem p)
    (hmax : ∀ I : Ideal S, Module.Finite R I → I ≤ Ideal.span ({p} : Set S))
    (m : M) : p • m = m := by
  obtain ⟨e, _, hecentral, hefinite, he⟩ := exists_finite_support R (S := S) (M := M)
  have hep : e * p = e := (mem_span_idempotent_iff hp).mp
    (hmax _ hefinite (Ideal.mem_span_singleton_self e))
  have hpe : p * e = e := by
    exact (hecentral.comm p).eq.symm.trans hep
  calc
    p • m = p • (e • m) := by rw [he]
    _ = (p * e) • m := (mul_smul p e m).symm
    _ = m := by rw [hpe, he]

private theorem finite_range_smul (R : Type*) {S : Type*} {T : Type*} {M : Type*}
    [CommRing R] [Ring S] [Ring T] [Algebra R S] [Algebra R T]
    [AddCommGroup M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower R T M] [SMulCommClass S T M]
    [Module.Finite S M] {p : S} (hp : IsIdempotentElem p) (hc : IsMulCentral p)
    [Module.Finite R (Ideal.span ({p} : Set S))] :
    Module.Finite R (LinearMap.range (Algebra.lsmul R T M p)) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  let P : Ideal S := Ideal.span {p}
  let π : M →ₗ[T] M := Algebra.lsmul R T M p
  let c : (Fin n → P) →ₗ[R] (Fin n → S) :=
    LinearMap.pi fun i ↦ (P.subtype.restrictScalars R).comp (LinearMap.proj i)
  let g : (Fin n → P) →ₗ[R] M := (f.restrictScalars R).comp c
  have hfixed (z : Fin n → P) : p • g z = g z := by
    change p • f (c z) = f (c z)
    rw [← f.map_smul]
    congr 1
    ext i
    change p * (z i : S) = (z i : S)
    rw [(hc.comm (z i : S)).eq, (mem_span_idempotent_iff hp).mp (z i).property]
  let g' : (Fin n → P) →ₗ[R] π.range :=
    g.codRestrict (π.range.restrictScalars R) fun z ↦ ⟨g z, hfixed z⟩
  apply Module.Finite.of_surjective g'
  intro y
  obtain ⟨m, hm⟩ := y.property
  obtain ⟨t, ht⟩ := hf m
  let z : Fin n → P := fun i ↦
    ⟨t i * p, P.mul_mem_left (t i) (Ideal.mem_span_singleton_self p)⟩
  refine ⟨z, Subtype.ext ?_⟩
  change f (c z) = (y : M)
  have hz : c z = p • t := by
    ext i
    exact (hc.comm (t i)).eq.symm
  rw [hz, f.map_smul, ht]
  exact hm

private theorem finite_supports_smul_eq (R : Type*) {S : Type*} {T : Type*} {M : Type*}
    [CommRing R] [IsNoetherianRing R] [Ring S] [Ring T]
    [Algebra R S] [Algebra R T] [IsSemisimpleRing S] [IsSemisimpleRing T]
    [AddCommGroup M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S M] [IsScalarTower R T M] [SMulCommClass S T M]
    [Module.Finite S M] [Module.Finite T M]
    {p : S} {q : T} (hp : IsIdempotentElem p) (hpc : IsMulCentral p)
    (hq : IsIdempotentElem q) (hqc : IsMulCentral q)
    [Module.Finite R (Ideal.span ({p} : Set S))]
    [Module.Finite R (Ideal.span ({q} : Set T))]
    (hmaxp : ∀ I : Ideal S, Module.Finite R I → I ≤ Ideal.span ({p} : Set S))
    (hmaxq : ∀ I : Ideal T, Module.Finite R I → I ≤ Ideal.span ({q} : Set T))
    (m : M) : p • m = q • m := by
  let : SMulCommClass T S M := SMulCommClass.symm _ _ _
  let π : M →ₗ[T] M := Algebra.lsmul R T M p
  let τ : M →ₗ[S] M := Algebra.lsmul R S M q
  let : Module.Finite R π.range := finite_range_smul R hp hpc
  let : Module.Finite R τ.range := finite_range_smul R hq hqc
  have hleft : q • (p • m) = p • m :=
    congrArg Subtype.val (support_eq_one R hq hmaxq (⟨p • m, m, rfl⟩ : π.range))
  have hright : p • (q • m) = q • m :=
    congrArg Subtype.val (support_eq_one R hp hmaxp (⟨q • m, m, rfl⟩ : τ.range))
  calc
    p • m = q • (p • m) := hleft.symm
    _ = p • (q • m) := smul_comm q p m
    _ = q • m := hright

private theorem opposite_support_eq (R : Type*) {S : Type*}
    [CommRing R] [IsNoetherianRing R] [Ring S] [Algebra R S]
    [IsSemisimpleRing S] {p : S} {q : Sᵐᵒᵖ}
    (hp : IsIdempotentElem p) (hpc : IsMulCentral p)
    (hq : IsIdempotentElem q) (hqc : IsMulCentral q)
    [Module.Finite R (Ideal.span ({p} : Set S))]
    [Module.Finite R (Ideal.span ({q} : Set Sᵐᵒᵖ))]
    (hmaxp : ∀ I : Ideal S, Module.Finite R I → I ≤ Ideal.span ({p} : Set S))
    (hmaxq : ∀ I : Ideal Sᵐᵒᵖ, Module.Finite R I → I ≤ Ideal.span ({q} : Set Sᵐᵒᵖ)) :
    q = MulOpposite.op p := by
  let f : Sᵐᵒᵖ →ₗ[Sᵐᵒᵖ] S := LinearMap.toSpanSingleton Sᵐᵒᵖ S 1
  let : Module.Finite Sᵐᵒᵖ S := Module.Finite.of_surjective f fun x ↦
    ⟨MulOpposite.op x, by change 1 * x = x; exact one_mul x⟩
  have h := finite_supports_smul_eq R hp hpc hq hqc hmaxp hmaxq (1 : S)
  change p * 1 = 1 * MulOpposite.unop q at h
  exact MulOpposite.unop_injective
    (by simpa only [mul_one, one_mul, MulOpposite.unop_op] using h.symm)

private theorem central_of_first_layer_commute {S : Type*} [Ring S]
    (I : Ideal S) [I.IsTwoSided] (hI : IsNilpotent I)
    {e : S} (he : IsIdempotentElem e)
    (hc : IsMulCentral (Ideal.Quotient.mk I e))
    (hcomm : ∀ x ∈ I, e * x - x * e ∈ I ^ 2) : IsMulCentral e := by
  refine he.isMulCentral_of_sandwich_mem_sq hI hc (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · simpa only [sub_mul, mul_assoc, he.mul_one_sub_self, mul_zero, sub_zero] using
      (I ^ 2).mul_mem_right (1 - e) (hcomm x hx)
  · have h : x * e - e * x ∈ I ^ 2 := by
      simpa only [neg_sub] using (I ^ 2).neg_mem (hcomm x hx)
    simpa only [mul_sub, ← mul_assoc, he.one_sub_mul_self, zero_mul, sub_zero] using
      (I ^ 2).mul_mem_left (1 - e) h

private theorem sup_pow_le {S : Type*} [Ring S]
    (I N : Ideal S) [N.IsTwoSided] (n : ℕ) : (I ⊔ N) ^ n ≤ I ^ n ⊔ N := by
  induction n with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, top_sup_eq, le_refl]
  | succ n ih =>
    rw [Submodule.pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, ← Submodule.pow_succ]
    exact sup_le
      (sup_le le_sup_left (Ideal.mul_le_right.trans le_sup_right))
      (sup_le (Ideal.mul_le_left.trans le_sup_right) (Ideal.mul_le_right.trans le_sup_right))

private theorem finite_span_of_finite_quotient_span (R : Type*) {S : Type*}
    [CommRing R] [Ring S] [Algebra R S] [IsNoetherianRing S]
    (I : Ideal S) [I.IsTwoSided] (hI : IsNilpotent I)
    {e : S} (he : IsIdempotentElem e) (hc : IsMulCentral e)
    [Module.Finite R (Ideal.span ({Ideal.Quotient.mk I e} : Set (S ⧸ I)))] :
    Module.Finite R (Ideal.span ({e} : Set S)) := by
  let M : Ideal S := Ideal.span {e}
  let N : Ideal S := Module.annihilator S M
  let H : Ideal S := I ⊔ N
  let : H.IsTwoSided := by
    refine ⟨fun {x} a hx ↦ ?_⟩
    obtain ⟨j, hj, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_mul]
    exact H.add_mem (Submodule.mem_sup_left (I.mul_mem_right a hj))
      (Submodule.mem_sup_right (N.mul_mem_right a hk))
  have hne : 1 - e ∈ N := by
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    change (1 - e) * (x : S) = 0
    have hxe : (x : S) * e = x := (mem_span_idempotent_iff he).mp x.property
    have hex : e * (x : S) = x := (hc.comm (x : S)).eq.trans hxe
    rw [sub_mul, one_mul, hex, sub_self]
  let φ : (S ⧸ I) →ₐ[R] (S ⧸ H) :=
    Ideal.Quotient.factorₐ R (show I ≤ H from le_sup_left)
  have heone : φ (Ideal.Quotient.mk I e) = 1 := by
    change Ideal.Quotient.mk H e = 1
    have hsub : e - 1 ∈ H := by
      simpa only [neg_sub] using H.neg_mem
        (show 1 - e ∈ H from (le_sup_right : N ≤ H) hne)
    simpa only [map_one] using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := H) e 1).mpr hsub
  let P : Ideal (S ⧸ I) := Ideal.span {Ideal.Quotient.mk I e}
  let f : P →ₗ[R] (S ⧸ H) := φ.toLinearMap.comp (P.subtype.restrictScalars R)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨⟨Ideal.Quotient.mk I a * Ideal.Quotient.mk I e,
      P.mul_mem_left _ (Ideal.mem_span_singleton_self _)⟩, ?_⟩
    change φ (Ideal.Quotient.mk I a * Ideal.Quotient.mk I e) = Ideal.Quotient.mk H a
    rw [map_mul, heone, mul_one]
    rfl
  let : Module.Finite R (S ⧸ H) := Module.Finite.of_surjective f hf
  obtain ⟨n, hn⟩ := hI
  have hH : H ^ n ≤ Module.annihilator S M := by
    exact (sup_pow_le I N n).trans
      (by simpa only [hn, Ideal.zero_eq_bot, bot_sup_eq] using (le_refl N))
  exact Ideal.finite_of_pow_le_annihilator (S := R) M H ⟨n, hH⟩

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

private theorem character_surjective (χ : A →ₐ[R] R) : Function.Surjective χ :=
  fun r ↦ ⟨algebraMap R A r, χ.commutes r⟩

private theorem character_eq_one_of_maximal_support [IsArtinianRing A]
    (χ : A →ₐ[R] R) {e : A} (he : IsIdempotentElem e)
    (hmax : ∀ I : Ideal (A ⧸ Ring.jacobson A), Module.Finite R I →
      I ≤ Ideal.span ({Ideal.Quotient.mk (Ring.jacobson A) e} : Set _)) : χ e = 1 := by
  let : IsArtinianRing R := (character_surjective χ).isArtinianRing
  let : RingHomSurjective χ.toRingHom := ⟨character_surjective χ⟩
  let J : Ideal A := Ring.jacobson A
  let K : Ideal R := Ring.jacobson R
  let ψ : (A ⧸ J) →ₐ[R] (R ⧸ K) :=
    Ideal.quotientMapₐ K χ (Ring.le_comap_jacobson χ.toRingHom)
  let : Module (A ⧸ J) (R ⧸ K) := Module.compHom (R ⧸ K) ψ.toRingHom
  let : IsScalarTower R (A ⧸ J) (R ⧸ K) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change ψ (algebraMap R (A ⧸ J) r) * x = r • x
      rw [ψ.commutes, Algebra.smul_def]
  have hψ : ψ (Ideal.Quotient.mk J e) = 1 := by
    have h := support_eq_one R (he.map (Ideal.Quotient.mk J)) hmax (1 : R ⧸ K)
    change ψ (Ideal.Quotient.mk J e) * 1 = 1 at h
    simpa only [mul_one] using h
  have hquot : Ideal.Quotient.mk K (χ e) = Ideal.Quotient.mk K 1 := by
    change Ideal.Quotient.mk K (χ e) = 1 at hψ
    simpa only [map_one] using hψ
  have hsub : χ e - 1 ∈ K := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hquot
  have hu : IsUnit (χ e) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (by
    rwa [Ideal.jacobson_bot])
  exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp (he.map χ)

/-- A character on an algebra that is Artinian on both sides is one on a central
idempotent whose principal left ideal is finitely generated over the base ring.

The base ring may be any commutative ring, including a nonreduced or zero ring.
The module structure on the ideal is inherited from the given algebra structure.
The whole algebra need not be finite over the base ring. -/
theorem exists_isIdempotentElem_isMulCentral_finite_span
    [IsArtinianRing A] [IsArtinianRing Aᵐᵒᵖ] (χ : A →ₐ[R] R) :
    ∃ e : A, IsIdempotentElem e ∧ IsMulCentral e ∧ χ e = 1 ∧
      Module.Finite R (Ideal.span ({e} : Set A)) := by
  let : IsArtinianRing R := (character_surjective χ).isArtinianRing
  let J : Ideal A := Ring.jacobson A
  have hJ : IsNilpotent J := IsSemiprimaryRing.isNilpotent
  obtain ⟨p, hp, hpc, hpfinite, hmaxp⟩ :=
    exists_maximal_finite_support R (S := A ⧸ J)
  obtain ⟨q, hq, hqc, hqfinite, hmaxq⟩ :=
    exists_maximal_finite_support R (S := (A ⧸ J)ᵐᵒᵖ)
  let : Module.Finite R (Ideal.span ({p} : Set (A ⧸ J))) := hpfinite
  let : Module.Finite R (Ideal.span ({q} : Set (A ⧸ J)ᵐᵒᵖ)) := hqfinite
  have hqop : q = MulOpposite.op p :=
    opposite_support_eq R hp hpc hq hqc hmaxp hmaxq
  have hnilker : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk J), IsNilpotent x := by
    obtain ⟨n, hn⟩ := hJ
    intro x hx
    have hxJ : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx
    refine ⟨n, ?_⟩
    have hpow : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hxJ n
    rw [hn] at hpow
    exact hpow
  obtain ⟨e, he, hep⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk J) hnilker p (Ideal.Quotient.mk_surjective p) hp
  let Q := J ⧸ Submodule.comap J.subtype (J ^ 2)
  have hcomm (x : A) (hx : x ∈ J) : e * x - x * e ∈ J ^ 2 := by
    let x' : J := ⟨x, hx⟩
    have hactions := finite_supports_smul_eq R hp hpc hq hqc hmaxp hmaxq
      (Submodule.Quotient.mk x' : Q)
    rw [hqop, ← hep] at hactions
    have hactions' :
        e • (Submodule.Quotient.mk x' : Q) =
          MulOpposite.op e • (Submodule.Quotient.mk x' : Q) := by
      simpa only [Ideal.quotient_mk_smul_squareQuotient,
        Ideal.op_quotient_mk_smul_squareQuotient] using hactions
    have hzero : (Submodule.comap J.subtype (J ^ 2)).mkQ
        (e • x' - MulOpposite.op e • x') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hactions'
    exact (Ideal.mk_squareQuotient_eq_zero J _).mp hzero
  have hecentral : IsMulCentral e := central_of_first_layer_commute J hJ he
    (by simpa only [hep] using hpc) hcomm
  have hmaxe : ∀ I : Ideal (A ⧸ J), Module.Finite R I →
      I ≤ Ideal.span ({Ideal.Quotient.mk J e} : Set (A ⧸ J)) := by
    simpa only [hep] using hmaxp
  let : Module.Finite R
      (Ideal.span ({Ideal.Quotient.mk J e} : Set (A ⧸ J))) := by
    rw [hep]
    exact hpfinite
  exact ⟨e, he, hecentral, character_eq_one_of_maximal_support χ he hmaxe,
    finite_span_of_finite_quotient_span R J hJ he hecentral⟩

end AlgHom

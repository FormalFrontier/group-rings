/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The ideal-action induction adapts Mathlib/RingTheory/HopkinsLevitzki.lean,
whose original notice is:
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length

/-!
# Scalar restriction across a nilpotent ideal action

Let `φ : S →+* A` be a homomorphism of arbitrary rings, and let `I` be a
two-sided ideal such that `S → A ⧸ I` is surjective. If a power of `I`
annihilates an `A`-module, restriction along `φ` preserves and reflects
Noetherianity and Artinianity and preserves composition length in `ℕ∞`.
In particular, this applies to every module when `I` is nilpotent.

Only the submodule lattices of the annihilated layers are identified. The
submodule lattices of the original module need not agree.

## References

The ideal-action induction generalizes Junyan Xu's formalization of
`IsSemiprimaryRing.induction` in Mathlib, retaining its submodule/quotient
argument but allowing any uniformly nilpotent ideal action. Length transport
uses Mathlib's semilinear submodule correspondence and Andrew Yang's
formalization of composition length and its exact-sequence additivity.
-/

@[expose] public section

universe uS uA uV uW

namespace LinearMap

variable {S : Type uS} {A : Type uA} [Ring S] [Ring A]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [AddCommGroup W]
variable [Module S V] [Module A W] {φ : S →+* A} [RingHomSurjective φ]

/-- A bijective semilinear map with surjective scalar map preserves composition
length, including infinite length. -/
theorem length_eq_of_bijective (f : V →ₛₗ[φ] W) (hf : Function.Bijective f) :
    Module.length S V = Module.length A W := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

end LinearMap

/-- The semilinear length comparison specializes to Mathlib's surjective
algebra-map comparison. -/
theorem Module.length_eq_of_surjective_algebraMap
    {S : Type uS} {A : Type uA} {V : Type uV}
    [CommRing S] [Ring A] [Algebra S A] [AddCommGroup V]
    [Module S V] [Module A V] [IsScalarTower S A V]
    (hφ : Function.Surjective (algebraMap S A)) :
    Module.length S V = Module.length A V := by
  let : RingHomSurjective (algebraMap S A) := ⟨hφ⟩
  let f : V →ₛₗ[algebraMap S A] V := ⟨AddHom.id V, by simp⟩
  exact f.length_eq_of_bijective Function.bijective_id

namespace Ideal

variable {S : Type uS} {A : Type uA} [Semiring S] [Ring A] [Module S A]
variable (V : Type uV) [AddCommGroup V] [Module S V] [Module A V]
variable [IsScalarTower S A V] (I : Ideal A)

/-- Induction through ideal-action layers under a uniform annihilator bound.
The base case is an `I`-annihilated module; the extension step uses `I • V`
and its quotient. Auxiliary compatible scalars are retained. -/
@[elab_as_elim]
theorem induction_on_pow_le_annihilator
    {P : ∀ (M : Type uV) [AddCommGroup M] [Module S M] [Module A M], Prop}
    (h0 : ∀ (M) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower S A M],
      Module.IsTorsionBySet A M I → P M)
    (h1 : ∀ (M) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower S A M],
      let N := I • (⊤ : Submodule A M); P N → P (M ⧸ N) → P M)
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) : P V := by
  obtain ⟨n, hn⟩ := hIV
  have base {M : Type uV} [AddCommGroup M] [Module S M] [Module A M]
      [IsScalarTower S A M] (h : I ≤ Module.annihilator A M) : P M := by
    apply h0 M
    rwa [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  induction n generalizing V with
  | zero =>
    rw [I.pow_zero, Ideal.one_eq_top] at hn
    exact base (le_top.trans hn)
  | succ n ih =>
    obtain _ | n := n
    · rw [I.pow_one] at hn
      exact base hn
    refine h1 V (ih _ ?_) (ih _ ?_)
    · rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff, I.pow_succ,
        Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
    · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
        Module.isTorsionBySet_quotient_iff]
      exact fun m i hi ↦ Submodule.smul_mem_smul (Ideal.pow_le_self n.succ_ne_zero hi) trivial

end Ideal

/-- Recovery of the semiprimary module-induction principle from uniform
ideal-action induction, with the same auxiliary scalar structures. -/
theorem IsSemiprimaryRing.induction_via_ideal
    (S : Type uS) (A : Type uA) (V : Type uV) [Ring S] [Ring A] [Module S A]
    [AddCommGroup V] [Module S V] [Module A V] [IsScalarTower S A V]
    [IsSemiprimaryRing A]
    {P : ∀ (M : Type uV) [AddCommGroup M] [Module S M] [Module A M], Prop}
    (h0 : ∀ (M) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower S A M]
      [IsSemisimpleModule A M], Module.IsTorsionBySet A M (Ring.jacobson A) → P M)
    (h1 : ∀ (M) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower S A M],
      let N := Ring.jacobson A • (⊤ : Submodule A M); P N → P (M ⧸ N) → P M) :
    P V := by
  obtain ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff A).mp inferInstance
  refine Ideal.induction_on_pow_le_annihilator (S := S) V (Ring.jacobson A)
    (P := P) ?_ h1 ⟨n, by rw [hn]; exact bot_le⟩
  intro M _ _ _ _ h
  let := h.module
  have := (h.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).2
    inferInstance
  exact h0 M h

namespace Ideal

variable {S : Type uS} {A : Type uA} [sRing : Ring S] [Ring A]
variable {V : Type uV} [vAdd : AddCommGroup V] [Module A V]
variable (φ : S →+* A) (I : Ideal A) [I.IsTwoSided]

private theorem comparison_of_torsion
    [Module S A] [Module S V] [IsScalarTower S A V]
    (hsmul : ∀ (s : S) (a : A), s • a = φ s * a)
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hV : Module.IsTorsionBySet A V I) :
    (IsNoetherian A V ↔ IsNoetherian S V) ∧
      (IsArtinian A V ↔ IsArtinian S V) ∧ Module.length A V = Module.length S V := by
  let := hV.module
  let : RingHomSurjective ((Ideal.Quotient.mk I).comp φ) := ⟨hφ⟩
  let f : V →ₛₗ[(Ideal.Quotient.mk I).comp φ] V :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun s x ↦ by
        change s • x = φ s • x
        simpa only [hsmul, mul_one, one_smul] using (smul_assoc s (1 : A) x).symm }
  exact ⟨(hV.semilinearMap.isNoetherian_iff_of_bijective Function.bijective_id).trans
      (f.isNoetherian_iff_of_bijective Function.bijective_id).symm,
    (hV.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).trans
      (f.isArtinian_iff_of_bijective Function.bijective_id).symm,
    (hV.semilinearMap.length_eq_of_bijective Function.bijective_id).trans
      (f.length_eq_of_bijective Function.bijective_id).symm⟩

private theorem comparison_of_pow_le_annihilator
    [Module S A] [Module S V] [IsScalarTower S A V]
    (hsmul : ∀ (s : S) (a : A), s • a = φ s * a)
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) :
    (IsNoetherian A V ↔ IsNoetherian S V) ∧
      (IsArtinian A V ↔ IsArtinian S V) ∧ Module.length A V = Module.length S V := by
  refine Ideal.induction_on_pow_le_annihilator (S := S) V I
    (P := fun M _ _ _ ↦ (IsNoetherian A M ↔ IsNoetherian S M) ∧
      (IsArtinian A M ↔ IsArtinian S M) ∧ Module.length A M = Module.length S M)
    (fun M _ _ _ _ h ↦ comparison_of_torsion φ I hsmul hφ h) ?_ hIV
  intro M _ _ _ _ N hN hQ
  let e := Submodule.Quotient.restrictScalarsEquiv S N
  have hN' : (IsNoetherian A N ↔ IsNoetherian S (N.restrictScalars S)) := hN.1
  have hA' : (IsArtinian A N ↔ IsArtinian S (N.restrictScalars S)) := hN.2.1
  have hQ' : IsNoetherian A (M ⧸ N) ↔ IsNoetherian S (M ⧸ N.restrictScalars S) :=
    hQ.1.trans (LinearMap.isNoetherian_iff_of_bijective e.toLinearMap e.bijective).symm
  have hQA' : IsArtinian A (M ⧸ N) ↔ IsArtinian S (M ⧸ N.restrictScalars S) :=
    hQ.2.1.trans (LinearMap.isArtinian_iff_of_bijective e.toLinearMap e.bijective).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [isNoetherian_iff_submodule_quotient N,
      isNoetherian_iff_submodule_quotient (N.restrictScalars S), hN', hQ']
  · rw [isArtinian_iff_submodule_quotient N,
      isArtinian_iff_submodule_quotient (N.restrictScalars S), hA', hQA']
  · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
        (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]),
      Module.length_eq_add_of_exact (N.restrictScalars S).subtype
        (N.restrictScalars S).mkQ (N.restrictScalars S).subtype_injective
        (N.restrictScalars S).mkQ_surjective
        (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]),
      hN.2.2, hQ.2.2, e.length_eq]
    rfl

/-- Uniform nilpotence of an ideal action implies that restriction across a map
surjective modulo that ideal preserves and reflects Noetherianity. -/
theorem isNoetherian_iff_of_pow_le_annihilator
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) :
    IsNoetherian A V ↔
      @IsNoetherian S V sRing.toSemiring vAdd.toAddCommMonoid (Module.compHom V φ) := by
  let := φ.toModule
  let := Module.compHom V φ
  let : IsScalarTower S A V := SMul.comp.isScalarTower φ
  exact (comparison_of_pow_le_annihilator φ I (fun _ _ ↦ rfl) hφ hIV).1

/-- Uniform nilpotence of an ideal action implies that restriction across a map
surjective modulo that ideal preserves and reflects Artinianity. -/
theorem isArtinian_iff_of_pow_le_annihilator
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) :
    IsArtinian A V ↔
      @IsArtinian S V sRing.toSemiring vAdd.toAddCommMonoid (Module.compHom V φ) := by
  let := φ.toModule
  let := Module.compHom V φ
  let : IsScalarTower S A V := SMul.comp.isScalarTower φ
  exact (comparison_of_pow_le_annihilator φ I (fun _ _ ↦ rfl) hφ hIV).2.1

/-- Uniform nilpotence of an ideal action implies equality of composition lengths
under restriction across a map surjective modulo that ideal, including `⊤`. -/
theorem length_eq_of_pow_le_annihilator
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) :
    Module.length A V = @Module.length S V sRing vAdd (Module.compHom V φ) := by
  let := φ.toModule
  let := Module.compHom V φ
  let : IsScalarTower S A V := SMul.comp.isScalarTower φ
  exact (comparison_of_pow_le_annihilator φ I (fun _ _ ↦ rfl) hφ hIV).2.2

/-- Restriction across a map surjective modulo a nilpotent two-sided ideal
preserves and reflects Noetherianity. -/
theorem isNoetherian_iff_of_isNilpotent
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ)) (hI : IsNilpotent I) :
    IsNoetherian A V ↔
      @IsNoetherian S V sRing.toSemiring vAdd.toAddCommMonoid (Module.compHom V φ) := by
  obtain ⟨n, hn⟩ := hI
  exact isNoetherian_iff_of_pow_le_annihilator φ I hφ ⟨n, hn ▸ bot_le⟩

/-- Restriction across a map surjective modulo a nilpotent two-sided ideal
preserves and reflects Artinianity. -/
theorem isArtinian_iff_of_isNilpotent
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ)) (hI : IsNilpotent I) :
    IsArtinian A V ↔
      @IsArtinian S V sRing.toSemiring vAdd.toAddCommMonoid (Module.compHom V φ) := by
  obtain ⟨n, hn⟩ := hI
  exact isArtinian_iff_of_pow_le_annihilator φ I hφ ⟨n, hn ▸ bot_le⟩

/-- Restriction across a map surjective modulo a nilpotent two-sided ideal
preserves composition length in `ℕ∞`, without a finite-length assumption. -/
theorem length_eq_of_isNilpotent
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ)) (hI : IsNilpotent I) :
    Module.length A V = @Module.length S V sRing vAdd (Module.compHom V φ) := by
  obtain ⟨n, hn⟩ := hI
  exact length_eq_of_pow_le_annihilator φ I hφ ⟨n, hn ▸ bot_le⟩

end Ideal

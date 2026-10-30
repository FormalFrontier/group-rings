/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Ideal.Annihilator
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Semisimplicity across a nilpotent ideal action

A uniformly nilpotent two-sided ideal action on a semisimple module vanishes.
The ideal itself need not be nilpotent: only one power must annihilate the given
module. More generally, the ideal action lies in the module's Jacobson radical.

For a ring map surjective modulo the ideal, an annihilated action has the same
semisimplicity after canonical scalar restriction. Consequently, under the
power bound, semisimplicity is equivalent to annihilation together with
semisimplicity of the restriction. The rings may be noncommutative or zero,
and the rings and module have independent universes.

## Implementation notes

The annihilation argument takes a complement of the existing common-annihilator
submodule and applies the common-annihilator theorem on that complement.
Restriction uses Mathlib's quotient action on set-torsion modules and its
semisimplicity transport along bijective semilinear maps. The module-radical
criterion uses Mathlib's Jacobson radical, including when there are no maximal
submodules; it does not identify radical vanishing with semisimplicity.
-/

@[expose] public section

universe uS uA uV

namespace Ideal

variable {A : Type uA} [Ring A]
variable {V : Type uV} [vAdd : AddCommGroup V] [Module A V]

/-- A uniformly nilpotent two-sided ideal action on a semisimple module is zero.
There is no finiteness or nontriviality assumption, and the exponent may be zero. -/
theorem le_annihilator_of_pow_le_annihilator [IsSemisimpleModule A V]
    (I : Ideal A) [I.IsTwoSided] {n : ℕ}
    (hI : I ^ n ≤ Module.annihilator A V) : I ≤ Module.annihilator A V := by
  obtain ⟨C, hC⟩ := exists_isCompl (annihilatorSubmodule V I)
  have hC0 : C = ⊥ := by
    by_contra hC0
    let : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hC0
    obtain ⟨x, hx, hIx⟩ := exists_ne_zero_le_torsionOf_of_pow_le_annihilator I
      (hI.trans (C.subtype.annihilator_le_of_injective C.subtype_injective))
    have hxK : (x : V) ∈ annihilatorSubmodule V I := by
      intro a ha
      exact congrArg Subtype.val ((mem_torsionOf_iff x a).mp (hIx ha))
    have hx0 : (x : V) = 0 := by
      have hxKC : (x : V) ∈ annihilatorSubmodule V I ⊓ C := ⟨hxK, x.property⟩
      simpa only [hC.inf_eq_bot, Submodule.mem_bot] using hxKC
    exact hx (Subtype.ext hx0)
  have hK : annihilatorSubmodule V I = ⊤ := by
    simpa only [hC0, sup_bot_eq] using hC.sup_eq_top
  have h := (le_annihilatorSubmodule_iff (N := (⊤ : Submodule A V))).mp hK.ge
  rwa [Submodule.annihilator_top] at h

/-- A uniformly nilpotent two-sided ideal action lies in the module's Jacobson
radical, without assuming the existence of any maximal submodule. -/
theorem smul_top_le_jacobson_of_pow_le_annihilator
    (I : Ideal A) [I.IsTwoSided] {n : ℕ}
    (hI : I ^ n ≤ Module.annihilator A V) :
    I • (⊤ : Submodule A V) ≤ Module.jacobson A V := by
  refine le_sInf fun N hN => ?_
  have : IsSimpleModule A (V ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  have hQ := le_annihilator_of_pow_le_annihilator I
    (hI.trans (N.mkQ.annihilator_le_of_surjective N.mkQ_surjective))
  have hT : Module.IsTorsionBySet A (V ⧸ N) I := by
    rwa [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact Submodule.smul_le.mpr fun a ha x _ =>
    (Module.isTorsionBySet_quotient_iff N I).mp hT x a ha

variable {S : Type uS} [sRing : Ring S]

/-- For an annihilated action, a scalar map surjective modulo the ideal preserves
and reflects semisimplicity under its canonical restriction. -/
theorem isSemisimpleModule_iff_of_le_annihilator
    (φ : S →+* A) (I : Ideal A) [I.IsTwoSided]
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hV : I ≤ Module.annihilator A V) :
    IsSemisimpleModule A V ↔
      @IsSemisimpleModule S sRing V vAdd (Module.compHom V φ) := by
  let : Module S V := Module.compHom V φ
  have hT : Module.IsTorsionBySet A V I := by
    rwa [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  let := hT.module
  let : RingHomSurjective ((Ideal.Quotient.mk I).comp φ) := ⟨hφ⟩
  let f : V →ₛₗ[(Ideal.Quotient.mk I).comp φ] V :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact hT.isSemisimpleModule_iff.symm.trans
    (f.isSemisimpleModule_iff_of_bijective Function.bijective_id).symm

/-- If an ideal action lies in the module radical, semisimplicity is equivalent
to annihilation and semisimplicity under canonical quotient-surjective scalar
restriction. No maximal-submodule existence hypothesis is required. -/
theorem isSemisimpleModule_iff_of_smul_top_le_jacobson
    (φ : S →+* A) (I : Ideal A) [I.IsTwoSided]
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hI : I • (⊤ : Submodule A V) ≤ Module.jacobson A V) :
    IsSemisimpleModule A V ↔ I ≤ Module.annihilator A V ∧
      @IsSemisimpleModule S sRing V vAdd (Module.compHom V φ) := by
  constructor
  · intro h
    let := h
    have hV : I ≤ Module.annihilator A V := by
      rw [← Submodule.annihilator_top, Submodule.le_annihilator_iff]
      exact le_bot_iff.mp (hI.trans (IsSemisimpleModule.jacobson_eq_bot A V).le)
    exact ⟨hV, (isSemisimpleModule_iff_of_le_annihilator φ I hφ hV).mp h⟩
  · rintro ⟨hV, h⟩
    exact (isSemisimpleModule_iff_of_le_annihilator φ I hφ hV).mpr h

/-- Under a uniform ideal-action power bound, a module is semisimple exactly
when the ideal annihilates it and its canonical scalar restriction is semisimple.
The scalar map need only be surjective modulo the ideal, not onto the ring. -/
theorem isSemisimpleModule_iff_of_pow_le_annihilator
    (φ : S →+* A) (I : Ideal A) [I.IsTwoSided]
    (hφ : Function.Surjective ((Ideal.Quotient.mk I).comp φ))
    (hIV : ∃ n : ℕ, I ^ n ≤ Module.annihilator A V) :
    IsSemisimpleModule A V ↔ I ≤ Module.annihilator A V ∧
      @IsSemisimpleModule S sRing V vAdd (Module.compHom V φ) := by
  obtain ⟨n, hn⟩ := hIV
  exact isSemisimpleModule_iff_of_smul_top_le_jacobson φ I hφ
    (smul_top_le_jacobson_of_pow_le_annihilator I hn)

end Ideal

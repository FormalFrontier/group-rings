/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Greatest submodules finite over restricted scalars

A Noetherian `A`-semimodule with a compatible action of a semiring `S` has a
unique greatest `A`-submodule that is finitely generated over `S`. This
submodule is preserved by every `A`-linear endomorphism. For the regular
module `A`, it is therefore a two-sided ideal.

No Noetherianity or commutativity of `S` is required. All scalar actions are
the given ones; only their compatibility is used. The generic submodule
results require merely an action of `S` on `A`, rather than an `S`-module
structure on `A`.

The proof uses the ascending chain condition on `A`-submodules and closure
of finite generation over `S` under binary suprema and linear images. It
does not require closure under arbitrary submodules, which can fail when
`S` is not Noetherian.
-/

@[expose] public section

universe uS uA uM

namespace Submodule

variable (S : Type uS) (A : Type uA) (M : Type uM)
variable [Semiring S] [Semiring A] [AddCommMonoid M]
variable [SMul S A] [Module S M] [Module A M] [IsScalarTower S A M]

/-- A Noetherian semimodule has a greatest submodule finite over compatible
restricted scalars. No Noetherianity of the smaller semiring is needed. -/
theorem exists_isGreatest_finite [IsNoetherian A M] :
    ∃ N : Submodule A M, IsGreatest {P : Submodule A M | Module.Finite S P} N := by
  have hbot : Module.Finite S (⊥ : Submodule A M) := by
    change Module.Finite S ((⊥ : Submodule A M).restrictScalars S)
    rw [restrictScalars_bot]
    infer_instance
  obtain ⟨N, hN⟩ := exists_maximal_of_wellFoundedGT
    (fun P : Submodule A M ↦ Module.Finite S P) ⟨⊥, hbot⟩
  refine ⟨N, hN.1, ?_⟩
  intro P hP
  have hsup : Module.Finite S (N ⊔ P : Submodule A M) := by
    change Module.Finite S ((N ⊔ P).restrictScalars S)
    rw [Module.Finite.iff_fg, restrictScalars_sup]
    exact (Module.Finite.iff_fg.mp hN.1).sup (Module.Finite.iff_fg.mp hP)
  exact le_sup_right.trans (hN.2 hsup le_sup_left)

variable {S A M}

/-- Every linear endomorphism preserves a greatest submodule finite over
compatible restricted scalars: its image is again finite over those scalars. -/
theorem map_le_of_isGreatest_finite {N : Submodule A M}
    (hN : IsGreatest {P : Submodule A M | Module.Finite S P} N) (f : M →ₗ[A] M) :
    N.map f ≤ N := by
  apply hN.2
  change Module.Finite S ((N.map f).restrictScalars S)
  rw [Module.Finite.iff_fg, restrictScalars_map]
  exact ((Module.Finite.iff_fg (N := N.restrictScalars S)).mp hN.1).map (f.restrictScalars S)

end Submodule

namespace Ideal

variable (S : Type uS) (A : Type uA)
variable [Semiring S] [Semiring A] [Module S A] [IsScalarTower S A A]

/-- A left-Noetherian semiring has a greatest left ideal finite over compatible
restricted scalars, and this ideal is two-sided. Right multiplications are
left-linear endomorphisms, so preserve the greatest finite left ideal. -/
theorem exists_isGreatest_finite [IsNoetherianRing A] :
    ∃ I : Ideal A, IsGreatest {J : Ideal A | Module.Finite S J} I ∧ I.IsTwoSided := by
  obtain ⟨I, hI⟩ := Submodule.exists_isGreatest_finite S A A
  refine ⟨I, hI, ⟨?_⟩⟩
  intro a b ha
  exact Submodule.map_le_of_isGreatest_finite hI (LinearMap.mulRight A b)
    (Submodule.mem_map_of_mem ha)

end Ideal

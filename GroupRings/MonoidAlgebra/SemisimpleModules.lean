/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Ideal.Semisimple
public import GroupRings.MonoidAlgebra.ModuleFiniteness
public import GroupRings.MonoidAlgebra.FixedVectors

/-!
# Semisimple modules of finite p-group algebras

For a finite `p`-group over any ring in which the prime `p` vanishes, a module
is semisimple exactly when its canonical coefficient restriction is semisimple
and every group symbol acts trivially. In particular, a semisimple module has
trivial canonical group action. No field, commutativity, dimension, finite
generation or nontriviality assumption is needed.

The proof applies the ideal-action semisimplicity criterion to the augmentation
kernel, using its cardinality nilpotence bound and the surjectivity of the
coefficient map modulo that kernel.
-/

@[expose] public section

universe uR uG uV

namespace MonoidAlgebra

variable {R : Type uR} [rRing : Ring R] {G : Type uG} [Group G] [Finite G]
variable {V : Type uV} [vAdd : AddCommGroup V] [Module (MonoidAlgebra R G) V]

/-- A module of a finite `p`-group algebra over a ring with prime `p = 0` is
semisimple exactly when its canonical coefficient restriction is semisimple
and every canonical group symbol fixes every vector. -/
theorem isSemisimpleModule_iff_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    IsSemisimpleModule (MonoidAlgebra R G) V ↔
      @IsSemisimpleModule R rRing V vAdd (moduleCoefficientModule R G V) ∧
      ∀ (g : G) (x : V), single g (1 : R) • x = x := by
  have h := Ideal.isSemisimpleModule_iff_of_pow_le_annihilator (V := V)
    (singleOneRingHom : R →+* MonoidAlgebra R G)
    (RingHom.ker (augmentation R G))
    (augmentation_quotient_singleOne_surjective (R := R) (M := G))
    ⟨Nat.card G, by rw [augmentation_pow_card_eq_bot hp hR hG]; exact bot_le⟩
  simpa only [moduleCoefficientModule, ker_augmentation_le_annihilator_iff, and_comm] using h

/-- Every canonical group symbol acts trivially on a semisimple module of a
finite `p`-group algebra over any ring in which the prime `p` vanishes. -/
theorem single_smul_eq_of_isSemisimpleModule_of_isPGroup
    [IsSemisimpleModule (MonoidAlgebra R G) V]
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G)
    (g : G) (x : V) : single g (1 : R) • x = x :=
  ((isSemisimpleModule_iff_of_isPGroup hp hR hG).mp inferInstance).2 g x

end MonoidAlgebra

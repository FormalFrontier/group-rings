/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite
public import GroupRings.RingTheory.Ideal.Annihilator

/-!
# Fixed vectors in monoid-algebra modules

For any ring and monoid, annihilation by the augmentation kernel is equivalent
to being fixed by every canonical symbol `single m 1`. Thus the kernel's
common-annihilator submodule describes the fixed vectors of the given module.

For a finite `p`-group over a ring in which the prime `p` vanishes, every
nontrivial unital module has a nonzero such vector. The augmentation nilpotence
bound and the common-annihilator theorem apply without coefficient commutativity,
finite generation, dimension, or finiteness of the module.

## References

For classical modular group-ring background, see D. S. Passman,
*The Algebraic Structure of Group Rings*, Wiley, 1977. Here the argument factors
through uniform nilpotence of the augmentation action over arbitrary rings.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

variable {R : Type u} [Ring R] {M : Type v} [Monoid M]
variable {V : Type w} [AddCommMonoid V] [Module (MonoidAlgebra R M) V]

/-- An arbitrary vector is annihilated by the augmentation kernel exactly when
every canonical monoid symbol fixes it. -/
theorem ker_augmentation_le_torsionOf_iff (x : V) :
    RingHom.ker (augmentation R M) ≤ Ideal.torsionOf (MonoidAlgebra R M) V x ↔
      ∀ m : M, single m (1 : R) • x = x := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup (MonoidAlgebra R M)
  rw [ker_augmentation, Ideal.span_le]
  constructor
  · intro h m
    have hm := (Ideal.mem_torsionOf_iff _ _).mp (h ⟨m, rfl⟩)
    simpa only [sub_smul, one_smul, sub_eq_zero] using hm
  · intro h y hy
    obtain ⟨m, rfl⟩ := hy
    apply (Ideal.mem_torsionOf_iff _ _).mpr
    simp only [sub_smul, one_smul, h m, sub_self]

/-- The augmentation kernel's common-annihilator submodule is the space of
vectors fixed by the canonical monoid symbols. The specialized simp rule takes
precedence over expansion to all scalars in the ideal. -/
@[simp 1100]
theorem mem_annihilatorSubmodule_ker_augmentation_iff (x : V) :
    x ∈ Ideal.annihilatorSubmodule V (RingHom.ker (augmentation R M)) ↔
      ∀ m : M, single m (1 : R) • x = x :=
  ker_augmentation_le_torsionOf_iff x

/-- The augmentation kernel annihilates the whole module exactly when every
canonical monoid symbol fixes every vector. -/
theorem ker_augmentation_le_annihilator_iff :
    RingHom.ker (augmentation R M) ≤ Module.annihilator (MonoidAlgebra R M) V ↔
      ∀ (m : M) (x : V), single m (1 : R) • x = x := by
  constructor
  · intro h m x
    apply (ker_augmentation_le_torsionOf_iff x).mp ?_ m
    intro a ha
    exact (Ideal.mem_torsionOf_iff x a).mpr (Module.mem_annihilator.mp (h ha) x)
  · intro h a ha
    exact Module.mem_annihilator.mpr fun x =>
      (Ideal.mem_torsionOf_iff x a).mp
        (((ker_augmentation_le_torsionOf_iff x).mpr fun m => h m x) ha)

variable {G : Type v} [Group G] [Finite G]
variable {W : Type w} [AddCommMonoid W] [Module (MonoidAlgebra R G) W] [Nontrivial W]

/-- For a finite `p`-group over any ring with prime `p = 0`, the submodule of
canonical fixed vectors is nonzero. -/
theorem annihilatorSubmodule_ker_augmentation_ne_bot_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    Ideal.annihilatorSubmodule W (RingHom.ker (augmentation R G)) ≠ ⊥ := by
  apply Ideal.annihilatorSubmodule_ne_bot_of_pow_le_annihilator (n := Nat.card G)
  rw [augmentation_pow_card_eq_bot hp hR hG]
  exact bot_le

/-- Every nontrivial unital module of a finite `p`-group algebra over any ring
with prime `p = 0` has a nonzero vector fixed by every canonical group symbol.
No finiteness or finite-generation hypothesis on the module is needed. -/
theorem exists_ne_zero_fixed_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    ∃ x : W, x ≠ 0 ∧ ∀ g : G, single g (1 : R) • x = x := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp
    (annihilatorSubmodule_ker_augmentation_ne_bot_of_isPGroup (W := W) hp hR hG)
  exact ⟨x, hx0, (mem_annihilatorSubmodule_ker_augmentation_iff x).mp hx⟩

end MonoidAlgebra

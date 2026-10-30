/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.FixedVectors
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple modules of finite p-group algebras

Over any ring in which the prime `p` vanishes, a simple module of a finite
`p`-group algebra has trivial group action. Its action therefore factors through
augmentation, and it is simple precisely when its restriction to the coefficient
ring is simple. The restriction is always the canonical one along
`singleOneRingHom`; no second scalar action or centrality assumption is needed.

The characteristic equivalence between augmentation action and trivial monoid
action holds already for semirings and semimodules. Simplicity is Mathlib's
`IsSimpleModule`; the ring can be noncommutative, and the module need not be
finite or finitely generated.

## References

For classical modular group-ring background, see D. S. Passman,
*The Algebraic Structure of Group Rings*, Wiley, 1977. The proof uses the
common-annihilator submodule of the nilpotent augmentation kernel and Mathlib's
transport of simplicity along bijective semilinear maps.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

section Semiring

variable {R : Type u} [Semiring R] {M : Type v} [Monoid M]
variable {V : Type w} [AddCommMonoid V] [Module (MonoidAlgebra R M) V]

/-- A monoid-algebra action is its augmentation acting through the coefficient
embedding exactly when every canonical monoid symbol fixes every vector. This
requires neither additive inverses nor commutative coefficients. -/
theorem smul_eq_augmentation_smul_iff :
    (∀ (a : MonoidAlgebra R M) (x : V),
      a • x = singleOneRingHom (M := M) (augmentation R M a) • x) ↔
      ∀ (m : M) (x : V), single m (1 : R) • x = x := by
  constructor
  · intro h m x
    simpa only [augmentation_single, map_one, one_smul] using h (single m 1) x
  · intro h a x
    refine induction_linear a (by simp) (fun a b ha hb => ?_) (fun m r => ?_)
    · simpa only [map_add, add_smul] using congrArg₂ (· + ·) ha hb
    · rw [augmentation_single, singleOneRingHom_apply]
      calc
        single m r • x = (single (1 : M) r * single m (1 : R)) • x := by simp
        _ = single (1 : M) r • x := by rw [mul_smul, h m x]

end Semiring

section Ring

variable {R : Type u} [Ring R] {M : Type v} [Monoid M]
variable {V : Type w} [AddCommGroup V] [Module (MonoidAlgebra R M) V]

/-- If a monoid-algebra module is simple under the canonical coefficient
restriction, it is simple over the monoid algebra. No condition on the monoid
or on its action is needed in this direction. -/
theorem isSimpleModule_of_isSimpleModule_singleOne
    (h : @IsSimpleModule R _ V _ (Module.compHom V (singleOneRingHom (M := M)))) :
    IsSimpleModule (MonoidAlgebra R M) V := by
  let : Module R V := Module.compHom V (singleOneRingHom (M := M))
  let : IsSimpleModule R V := h
  have : Nontrivial V := IsSimpleModule.nontrivial R V
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance, fun x hx y => ?_⟩
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective R hx y
  exact ⟨singleOneRingHom r, hr⟩

/-- When all monoid symbols act trivially, simplicity over a monoid algebra is
equivalent to simplicity under canonical restriction to its coefficient ring.
The semilinear scalar map used for transport is the surjective augmentation. -/
theorem isSimpleModule_iff_of_single_smul_eq
    (h : ∀ (m : M) (x : V), single m (1 : R) • x = x) :
    IsSimpleModule (MonoidAlgebra R M) V ↔
      @IsSimpleModule R _ V _ (Module.compHom V (singleOneRingHom (M := M))) := by
  let : Module R V := Module.compHom V (singleOneRingHom (M := M))
  let : RingHomSurjective (augmentation R M) := ⟨augmentation_surjective R M⟩
  let f : V →ₛₗ[augmentation R M] V :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => smul_eq_augmentation_smul_iff.mpr h a x }
  exact f.isSimpleModule_iff_of_bijective Function.bijective_id

variable {G : Type v} [Group G] [Finite G]
variable {W : Type w} [AddCommGroup W] [Module (MonoidAlgebra R G) W]

/-- In a simple module of a finite `p`-group algebra over a ring in which the
prime `p` vanishes, every canonical group symbol fixes every vector. -/
theorem single_smul_eq_of_isSimpleModule_of_isPGroup
    [IsSimpleModule (MonoidAlgebra R G) W]
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G)
    (g : G) (x : W) : single g (1 : R) • x = x := by
  have : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra R G) W
  have htop : Ideal.annihilatorSubmodule W (RingHom.ker (augmentation R G)) = ⊤ :=
    (eq_bot_or_eq_top _).resolve_left
      (annihilatorSubmodule_ker_augmentation_ne_bot_of_isPGroup hp hR hG)
  have hx : x ∈ Ideal.annihilatorSubmodule W (RingHom.ker (augmentation R G)) := by
    rw [htop]
    exact Submodule.mem_top
  exact (mem_annihilatorSubmodule_ker_augmentation_iff x).mp hx g

/-- Every scalar acts on a simple module of a finite `p`-group algebra through
augmentation and the canonical coefficient embedding, over any ring with
prime `p = 0`. -/
theorem smul_eq_augmentation_smul_of_isSimpleModule_of_isPGroup
    [IsSimpleModule (MonoidAlgebra R G) W]
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G)
    (a : MonoidAlgebra R G) (x : W) :
    a • x = singleOneRingHom (M := G) (augmentation R G a) • x :=
  smul_eq_augmentation_smul_iff.mpr
    (single_smul_eq_of_isSimpleModule_of_isPGroup hp hR hG) a x

/-- For a finite `p`-group over any ring in which the prime `p` vanishes, a
module is simple over the group algebra if and only if it is simple under the
canonical coefficient restriction. No nontriviality or finiteness hypothesis
on the module is required. -/
theorem isSimpleModule_iff_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    IsSimpleModule (MonoidAlgebra R G) W ↔
      @IsSimpleModule R _ W _ (Module.compHom W (singleOneRingHom (M := G))) := by
  constructor
  · intro h
    let := h
    exact (isSimpleModule_iff_of_single_smul_eq
      (single_smul_eq_of_isSimpleModule_of_isPGroup hp hR hG)).mp h
  · exact isSimpleModule_of_isSimpleModule_singleOne

end Ring

end MonoidAlgebra

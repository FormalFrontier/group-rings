/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.RingTheory.Ideal.ScalarRestriction
public import GroupRings.MonoidAlgebra.AugmentationNilpotence.Finite
public import GroupRings.MonoidAlgebra.AugmentationCrossedMaps

/-!
# Chain conditions and length of finite p-group modules

For any ring `R` in which a prime `p` vanishes and any finite `p`-group `G`,
an arbitrary given `R[G]`-module is Noetherian (respectively Artinian) exactly
when its canonical coefficient restriction is. Their composition lengths agree
in `ℕ∞`, including infinite length. Coefficients need not commute, and no
finiteness condition on the module or triviality of its group action is required.

## References

For classical modular group-ring background, see D. S. Passman,
*The Algebraic Structure of Group Rings*, Wiley, 1977. These comparisons use
the augmentation nilpotence theorem and the generic uniform ideal-action
scalar-restriction comparison, rather than another augmentation construction.
-/

@[expose] public section

universe uR uG uV

namespace MonoidAlgebra

variable {R : Type uR} [rRing : Ring R]

/-- Coefficients surject onto the quotient by the augmentation kernel.
The coefficient embedding into the monoid algebra itself need not be surjective. -/
theorem augmentation_quotient_singleOne_surjective {M : Type uG} [Monoid M] :
    Function.Surjective
      ((Ideal.Quotient.mk (RingHom.ker (augmentation R M))).comp
        (singleOneRingHom : R →+* MonoidAlgebra R M)) := by
  let e := (augmentation R M).quotientKerEquivOfSurjective (augmentation_surjective R M)
  intro x
  refine ⟨e x, e.injective ?_⟩
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk
    (augmentation_surjective R M) (single 1 (e x))).trans (augmentation_single R M 1 (e x))

variable {G : Type uG} [Group G] [Finite G]
variable {V : Type uV} [vAdd : AddCommGroup V] [Module (MonoidAlgebra R G) V]

/-- A module of a finite `p`-group algebra in characteristic `p` is Noetherian
exactly when its canonical coefficient restriction is Noetherian. The coefficient
ring may be noncommutative or zero. -/
theorem isNoetherian_iff_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    IsNoetherian (MonoidAlgebra R G) V ↔
      @IsNoetherian R V rRing.toSemiring vAdd.toAddCommMonoid
        (moduleCoefficientModule R G V) := by
  simpa only [moduleCoefficientModule] using
    (Ideal.isNoetherian_iff_of_isNilpotent (V := V)
      (singleOneRingHom : R →+* MonoidAlgebra R G)
      (RingHom.ker (augmentation R G))
      (augmentation_quotient_singleOne_surjective (R := R) (M := G))
      ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩)

/-- A module of a finite `p`-group algebra in characteristic `p` is Artinian
exactly when its canonical coefficient restriction is Artinian, without any
finite-generation hypothesis. -/
theorem isArtinian_iff_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    IsArtinian (MonoidAlgebra R G) V ↔
      @IsArtinian R V rRing.toSemiring vAdd.toAddCommMonoid
        (moduleCoefficientModule R G V) := by
  simpa only [moduleCoefficientModule] using
    (Ideal.isArtinian_iff_of_isNilpotent (V := V)
      (singleOneRingHom : R →+* MonoidAlgebra R G)
      (RingHom.ker (augmentation R G))
      (augmentation_quotient_singleOne_surjective (R := R) (M := G))
      ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩)

/-- Composition length over a finite `p`-group algebra in characteristic `p`
is the length under the canonical coefficient restriction. This is ring-relative
length in `ℕ∞`, not dimension over an underlying field, and may be infinite. -/
theorem length_eq_of_isPGroup
    {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0) (hG : IsPGroup p G) :
    Module.length (MonoidAlgebra R G) V =
      @Module.length R V rRing vAdd (moduleCoefficientModule R G V) := by
  simpa only [moduleCoefficientModule] using
    (Ideal.length_eq_of_isNilpotent (V := V)
      (singleOneRingHom : R →+* MonoidAlgebra R G)
      (RingHom.ker (augmentation R G))
      (augmentation_quotient_singleOne_surjective (R := R) (M := G))
      ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩)

end MonoidAlgebra

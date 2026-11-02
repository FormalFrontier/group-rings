/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.RingTheory.Artinian.Defs

import GroupRings.MonoidAlgebra.CoefficientChange
import GroupRings.MonoidAlgebra.FiniteCoefficientIdeal
import GroupRings.MonoidAlgebra.Units
import GroupRings.RingTheory.Artinian.FiniteCharacterBlock
import GroupRings.RingTheory.SimpleRing.Quotient
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Opposite
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.SimpleRing.Field

/-!
# Left-Artinian monoid and group algebras

For any ring `R` and right-cancellative monoid `G`, the monoid algebra `R[G]`
is left Artinian exactly when `R` is left Artinian and either `R` is
subsingleton or `G` is finite. In particular, over a nontrivial coefficient
ring, left Artinianity forces the monoid to be finite. This includes the
classical group-algebra criterion. The coefficients need not commute.

For a monoid algebra over a nontrivial semiring, left Artinianity makes each
right-regular monoid element a unit. This reduces the right-cancellative
monoid criterion over rings to the group case.

The subsingleton alternative includes the zero monoid algebra of an infinite
monoid over the zero ring. All chain conditions here concern left regular
modules over the respective semirings, not the monoid algebra merely as a module
over its coefficients. The coefficient and monoid universes are independent.
The local unit theorem allows semiring coefficients, but the global criterion
requires a ring: finite-module Artinian ascent does not hold over all semirings.

## Proof strategy

Right multiplication by `single m 1` reindexes coefficients by `x ↦ x * m`.
Right regularity of `m` therefore makes this multiplication injective.
Mathlib's Artinian regular-element criterion makes the basis term a unit,
and single-term unit reflection makes `m` a unit. For a right-cancellative
monoid, every element is thus in the image of the canonical units group.
Its coercion is a multiplicative equivalence; the induced ring equivalence
transports Artinianity to the group algebra without changing monoid operations.

For the group criterion, pass to a nonzero simple two-sided quotient of the coefficients. Its centre
is a field, and a right-linear coefficient retraction descends left Artinianity
to the group algebra over that field. Only there do group inversion and
commutativity of the coefficients give right Artinianity. The finite-character
block theorem then supplies a nonzero left ideal finite over the field, and
the finite-support criterion forces the group to be finite. No finite degree
over the centre or right-Artinian hypothesis on the original ring is used.

The converse uses Mathlib's finite coefficient-module instance and finite-module
Artinian ascent; coefficient necessity uses the surjective augmentation.

## References

* D. S. Passman, *The Algebraic Structure of Group Rings*, Wiley, 1977:
  the classical Artinian group-ring criterion. The proof here uses the simple-quotient
  reduction and the finite-character block argument described above.
* Mathlib, `Mathlib.RingTheory.SimpleRing.Field` and
  `Mathlib.RingTheory.Artinian.Module`: the centre field and Artinian transport.
* `GroupRings.RingTheory.Artinian.FiniteCharacterBlock` and
  `GroupRings.MonoidAlgebra.FiniteCoefficientIdeal`: the finite ideal and support arguments.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

section Group

variable {R : Type u} {G : Type v} [Ring R] [Group G]

private theorem finite_of_isArtinianRing_field {K : Type u} [Field K]
    [IsArtinianRing (MonoidAlgebra K G)] : Finite G := by
  -- Inversion reverses the group multiplication; the coefficient opposite is
  -- identified with the coefficients only because `K` is commutative.
  have hop : Function.Surjective
      (mapRingHom G (RingEquiv.toOpposite K).toRingHom) :=
    map_surjective (RingEquiv.toOpposite K).toRingHom.toAddMonoidHom
      (RingEquiv.toOpposite K).surjective
  let : IsArtinianRing (MonoidAlgebra Kᵐᵒᵖ G) := hop.isArtinianRing
  let eop : (MonoidAlgebra K G)ᵐᵒᵖ ≃+* MonoidAlgebra Kᵐᵒᵖ G :=
    (MonoidAlgebra.opRingEquiv (R := K) (M := G)).trans
      (mapDomainRingEquiv Kᵐᵒᵖ (MulEquiv.inv' G).symm)
  let : IsArtinianRing (MonoidAlgebra K G)ᵐᵒᵖ := eop.symm.isArtinianRing
  let χ : MonoidAlgebra K G →ₐ[K] K :=
    { toRingHom := augmentation K G
      commutes' := fun k => by
        change augmentation K G (algebraMap K (MonoidAlgebra K G) k) = k
        simpa only [Algebra.algebraMap_eq_smul_one, one_def, smul_single,
          smul_eq_mul, mul_one] using augmentation_single K G 1 k }
  obtain ⟨e, -, -, hχ, hfinite⟩ :=
    χ.exists_isIdempotentElem_isMulCentral_finite_span
  have he : e ≠ 0 := by
    intro he
    exact zero_ne_one (by simpa only [he, map_zero] using hχ)
  let I : Ideal (MonoidAlgebra K G) := Ideal.span ({e} : Set (MonoidAlgebra K G))
  let : Module.Finite K I := hfinite
  let : Module.Finite K (I.restrictScalars K) :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv K _ _ I).restrictScalars K).symm
  apply finite_of_moduleFinite_ideal I
  intro h
  exact he (Ideal.span_singleton_eq_bot.mp h)

private theorem finite_of_isArtinianRing_of_group [Nontrivial R]
    [IsArtinianRing (MonoidAlgebra R G)] : Finite G := by
  obtain ⟨c, hc⟩ := RingCon.exists_isSimpleRing_quotient (R := R)
  let S := c.Quotient
  let : IsSimpleRing S := hc
  have hq : Function.Surjective (mapRingHom G c.mk') :=
    map_surjective c.mk'.toAddMonoidHom c.mk'_surjective
  let : IsArtinianRing (MonoidAlgebra S G) := hq.isArtinianRing
  let K := Subring.center S
  let : Field K := (IsSimpleRing.isField_center S).toField
  let : IsArtinianRing (MonoidAlgebra K G) :=
    isArtinianRing_of_divisionRing_hom (M := G) (algebraMap K S)
  exact finite_of_isArtinianRing_field (K := K)

end Group

/-- A right-regular monoid element is a unit if its monoid algebra over a
nontrivial semiring is left Artinian. The monoid need not be cancellative. -/
theorem isUnit_of_isRightRegular_of_isArtinianRing (R : Type u) {M : Type v}
    [Semiring R] [Monoid M] [Nontrivial R] [IsArtinianRing (MonoidAlgebra R M)]
    (m : M) (hm : IsRightRegular m) : IsUnit m := by
  -- Recover each original coefficient at its injectively reindexed position.
  have hcoeff (f : MonoidAlgebra R M) (x : M) :
      (f * single m (1 : R)).coeff (x * m) = f.coeff x := by
    simpa only [mul_one] using coeff_mul_single_eq_coeff_mul (r := (1 : R)) x
      (fun y _ => ⟨fun h => hm h, fun h => congrArg (· * m) h⟩)
  have hregular : IsRightRegular (single m (1 : R)) := by
    intro f g h
    ext x
    simpa only [hcoeff] using congrArg (fun a : MonoidAlgebra R M => a.coeff (x * m)) h
  exact ((isUnit_single_iff m (1 : R)).mp
    (IsArtinianRing.isUnit_iff_isRightRegular.mpr hregular)).2

variable {R : Type u} {G : Type v} [Ring R] [Monoid G] [IsRightCancelMul G]

/-- A left-Artinian right-cancellative monoid algebra over a nontrivial ring
has a finite index monoid. The proof reduces through the canonical units group
to the classical Artinian group-ring criterion; see Passman,
*The Algebraic Structure of Group Rings*. -/
theorem finite_of_isArtinianRing [Nontrivial R]
    [IsArtinianRing (MonoidAlgebra R G)] : Finite G := by
  have hsurj : Function.Surjective (Units.coeHom G) := by
    intro g
    obtain ⟨u, hu⟩ := isUnit_of_isRightRegular_of_isArtinianRing R g (.all g)
    exact ⟨u, hu⟩
  let e : Gˣ ≃* G :=
    MulEquiv.ofBijective (Units.coeHom G) ⟨Units.coeHom_injective, hsurj⟩
  let : IsArtinianRing (MonoidAlgebra R Gˣ) :=
    (mapDomainRingEquiv R e).symm.isArtinianRing
  let : Finite Gˣ := finite_of_isArtinianRing_of_group (R := R)
  exact Finite.of_surjective (Units.coeHom G) hsurj

/-- A right-cancellative monoid algebra is left Artinian exactly when its
coefficient ring is left Artinian and either that ring is subsingleton or the
monoid is finite. No coefficient commutativity or right-Artinian hypothesis
is required. For groups this is the classical Artinian group-ring criterion;
see Passman, *The Algebraic Structure of Group Rings*. -/
theorem isArtinianRing_iff :
    IsArtinianRing (MonoidAlgebra R G) ↔
      IsArtinianRing R ∧ (Subsingleton R ∨ Finite G) := by
  constructor
  · intro h
    let : IsArtinianRing (MonoidAlgebra R G) := h
    refine ⟨(augmentation_surjective R G).isArtinianRing, ?_⟩
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    · let : Nontrivial R := hR
      exact Or.inr (finite_of_isArtinianRing (R := R))
  · rintro ⟨hR, h | h⟩
    · let : Subsingleton R := h
      exact isArtinian_of_finite (R := MonoidAlgebra R G) (M := MonoidAlgebra R G)
    · let : IsArtinianRing R := hR
      let : Finite G := h
      exact IsArtinianRing.of_finite R (MonoidAlgebra R G)

end MonoidAlgebra

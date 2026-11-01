/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.Augmentation
public import Mathlib.RingTheory.Artinian.Defs

import GroupRings.MonoidAlgebra.CoefficientChange
import GroupRings.MonoidAlgebra.FiniteCoefficientIdeal
import GroupRings.RingTheory.Artinian.FiniteCharacterBlock
import GroupRings.RingTheory.SimpleRing.Quotient
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Opposite
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.SimpleRing.Field

/-!
# Left-Artinian group algebras

For any ring `R` and group `G`, the group algebra `R[G]` is left Artinian exactly
when `R` is left Artinian and either `R` is subsingleton or `G` is finite. In
particular, over a nontrivial coefficient ring, left Artinianity forces the
group to be finite. The coefficients need not commute.

The subsingleton alternative includes the zero group algebra of an infinite
group over the zero ring. All chain conditions here concern left regular
modules over the respective rings, not the group algebra merely as a module
over its coefficient ring. The coefficient and group universes are independent.

## Proof strategy

Pass to a nonzero simple two-sided quotient of the coefficients. Its centre
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

/-- A left-Artinian group algebra over a nontrivial ring has a finite group.
This is the necessity direction of the classical Artinian group-ring criterion;
see Passman, *The Algebraic Structure of Group Rings*. -/
theorem finite_of_isArtinianRing [Nontrivial R]
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

/-- A group algebra is left Artinian exactly when its coefficient ring is left
Artinian and either the coefficient ring is subsingleton or the group is finite.
No commutativity or right-Artinian hypothesis is required. This is the classical
Artinian group-ring criterion; see Passman, *The Algebraic Structure of Group Rings*. -/
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

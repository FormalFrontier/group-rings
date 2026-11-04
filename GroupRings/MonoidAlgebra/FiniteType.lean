/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.FiniteType

/-!
# Finite type of monoid algebras over commutative semirings

For any commutative semiring `R` and monoid `M`, the canonical coefficient algebra
`MonoidAlgebra R M` is of finite type exactly when `M` is finitely generated or
`R` is subsingleton. Under nontrivial coefficients this is precisely finite
generation of `M`. The monoid need not be commutative, cancellative or a group,
and the coefficient and exponent universes are independent.

The additive-monoid criteria use the coefficient-preserving multiplicative
type-tag equivalence. Finite generation gives forward finite-type instances;
there is no converse finite-generation instance.

## References

The support extraction generalizes Johan Commelin's
`MonoidAlgebra.exists_finset_adjoin_eq_top` in `Mathlib.RingTheory.FiniteType`.
The support-span argument follows that module's
`AddMonoidAlgebra.finiteType_iff_fg`, on which its multiplicative
`MonoidAlgebra.finiteType_iff_fg` also depends, extending the coefficient class
from commutative rings to commutative semirings. The proof reuses the existing
semiring support-generation and free-algebra surjectivity theorems, together
with `Algebra.adjoin_eq_span` and
`MonoidAlgebra.mem_closure_of_mem_span_closure`.
-/

@[expose] public section

universe uR uM

namespace Algebra.FiniteType

/-- The algebra of a finitely generated monoid is of finite type over any
commutative semiring. This extends `MonoidAlgebra.finiteType_of_fg` beyond rings. -/
instance (priority := 100) monoidAlgebra
    (R : Type uR) (M : Type uM) [CommSemiring R] [Monoid M] [Monoid.FG M] :
    Algebra.FiniteType R (MonoidAlgebra R M) := by
  obtain ⟨S, hS⟩ := Monoid.FG.fg_top (M := M)
  exact Algebra.FiniteType.of_surjective
    (FreeAlgebra.lift R fun s : (S : Set M) => MonoidAlgebra.of R M s)
    (MonoidAlgebra.freeAlgebra_lift_of_surjective_of_closure hS)

end Algebra.FiniteType

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} [CommSemiring R] [Monoid M]

/-- Finite type over a commutative semiring gives finitely many monoid labels
whose coefficient-one terms generate the algebra. This generalizes
`MonoidAlgebra.exists_finset_adjoin_eq_top` from commutative rings. -/
theorem exists_finset_adjoin_eq_top_of_finiteType
    (h : Algebra.FiniteType R (MonoidAlgebra R M)) :
    ∃ S : Finset M, Algebra.adjoin R (of R M '' (S : Set M)) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := h.out
  refine ⟨S.biUnion fun f => f.coeff.support, ?_⟩
  rw [Finset.coe_biUnion]
  exact support_gen_of_gen' hS

/-- A monoid algebra over a commutative semiring is of finite type exactly when
the monoid is finitely generated or the coefficients are subsingleton.
This extends Mathlib's `MonoidAlgebra.finiteType_iff_fg` from nontrivial
commutative rings and includes the zero-coefficient case. -/
theorem finiteType_iff_fg_or_subsingleton :
    Algebra.FiniteType R (MonoidAlgebra R M) ↔ Monoid.FG M ∨ Subsingleton R := by
  constructor
  · intro h
    cases subsingleton_or_nontrivial R with
    | inl hR => exact Or.inr hR
    | inr hR =>
      let _ : Nontrivial R := hR
      obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top_of_finiteType h
      refine Or.inl (Monoid.fg_def.2 ⟨S, (Submonoid.eq_top_iff' _).2 fun m => ?_⟩)
      have hm : of R M m ∈
          (Algebra.adjoin R (of R M '' (S : Set M))).toSubmodule := by
        simp only [hS, Algebra.top_toSubmodule, Submodule.mem_top]
      rw [Algebra.adjoin_eq_span] at hm
      exact mem_closure_of_mem_span_closure hm
  · rintro (hM | hR)
    · let _ : Monoid.FG M := hM
      exact Algebra.FiniteType.monoidAlgebra R M
    · let _ : Subsingleton R := hR
      let _ : Subsingleton (MonoidAlgebra R M) := Algebra.subsingleton R _
      let _ : Module.Finite R (MonoidAlgebra R M) := Module.Finite.of_finite
      exact Module.Finite.finiteType _

/-- Over nontrivial commutative semirings, finite type of the canonical monoid
algebra is equivalent to finite generation of the monoid. For commutative rings
this recovers Mathlib's `MonoidAlgebra.finiteType_iff_fg`. -/
theorem finiteType_iff_fg_of_nontrivial [Nontrivial R] :
    Algebra.FiniteType R (MonoidAlgebra R M) ↔ Monoid.FG M := by
  simpa only [not_subsingleton R, or_false] using
    (finiteType_iff_fg_or_subsingleton (R := R) (M := M))

end MonoidAlgebra

namespace Algebra.FiniteType

/-- The algebra of a finitely generated additive monoid is of finite type over
any commutative semiring, by the coefficient-preserving multiplicative type tag. -/
instance (priority := 100) addMonoidAlgebra
    (R : Type uR) (M : Type uM) [CommSemiring R] [AddMonoid M] [AddMonoid.FG M] :
    Algebra.FiniteType R (AddMonoidAlgebra R M) :=
  (Algebra.FiniteType.monoidAlgebra R (Multiplicative M)).equiv
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R M).symm

end Algebra.FiniteType

namespace AddMonoidAlgebra

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddMonoid M]

/-- An additive monoid algebra over a commutative semiring is of finite type
exactly when the additive monoid is finitely generated or the coefficients
are subsingleton. This is the multiplicative criterion transported through
Mathlib's coefficient-preserving type-tag equivalence. -/
theorem finiteType_iff_fg_or_subsingleton :
    Algebra.FiniteType R (AddMonoidAlgebra R M) ↔ AddMonoid.FG M ∨ Subsingleton R := by
  have hfinite : Algebra.FiniteType R (AddMonoidAlgebra R M) ↔
      Algebra.FiniteType R (MonoidAlgebra R (Multiplicative M)) :=
    ⟨fun h => h.equiv (toMultiplicativeAlgEquiv R R M),
      fun h => h.equiv (toMultiplicativeAlgEquiv R R M).symm⟩
  rw [hfinite, MonoidAlgebra.finiteType_iff_fg_or_subsingleton,
    ← AddMonoid.fg_iff_mul_fg]

/-- Over nontrivial commutative semirings, finite type of the canonical additive
monoid algebra is equivalent to finite generation of the additive monoid.
For commutative rings this recovers Mathlib's `AddMonoidAlgebra.finiteType_iff_fg`. -/
theorem finiteType_iff_fg_of_nontrivial [Nontrivial R] :
    Algebra.FiniteType R (AddMonoidAlgebra R M) ↔ AddMonoid.FG M := by
  simpa only [not_subsingleton R, or_false] using
    (finiteType_iff_fg_or_subsingleton (R := R) (M := M))

end AddMonoidAlgebra

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.ModuleRepresentationEquiv
public import GroupTheory.RepresentationLifting
public import Mathlib.Algebra.Module.Projective

/-!
# Projectivity from coefficient projectivity

For a finite group whose order is a unit in the coefficient semiring, projectivity
over the canonical coefficient restriction implies projectivity of the original
group-algebra module. The coefficient semiring may be noncommutative or zero, and
its modules need only be additive commutative monoids. All universes are independent.

The proof first obtains a coefficient-linear lift using Mathlib's projectivity
lifting property, then applies GroupTheory's given-lift averaging theorem and the
Hom correspondence on the original modules. The free-cover characterization of
projectivity avoids any smallness hypothesis.

## References

The proof uses Mathlib's `Module.projective_lifting_property` and
`Module.Projective.of_lifting_property''`, and GroupTheory's
`Representation.exists_intertwining_lift`. The latter extends the averaging
construction in Mathlib's `Mathlib.RepresentationTheory.Maschke` to given linear
lifts over arbitrary semirings.
-/

@[expose] public section

universe uR uG uV

namespace MonoidAlgebra

/-- If the order of a finite group is a unit in the coefficient semiring, a given
group-algebra module that is projective for its canonical coefficient action is
projective over the group algebra. No commutativity, nontriviality or smallness
hypothesis is required. -/
theorem projective_of_coefficient_projective
    {R : Type uR} [Semiring R] {G : Type uG} [Group G] [Finite G]
    {V : Type uV} [AddCommMonoid V] [Module (MonoidAlgebra R G) V]
    (hcard : IsUnit (Nat.card G : R))
    (hV : @Module.Projective R _ V _ (moduleCoefficientModule R G V)) :
    Module.Projective (MonoidAlgebra R G) V := by
  apply Module.Projective.of_lifting_property''
  intro q hq
  let : Module R V := moduleCoefficientModule R G V
  let : Module R (V →₀ MonoidAlgebra R G) :=
    moduleCoefficientModule R G (V →₀ MonoidAlgebra R G)
  let : Module.Projective R V := hV
  obtain ⟨l, hl⟩ := Module.projective_lifting_property
    (moduleRepresentationMap R G q).toLinearMap
    (moduleRepresentationMap R G (LinearMap.id : V →ₗ[MonoidAlgebra R G] V)).toLinearMap hq
  apply (exists_linear_lift_iff_exists_intertwining_lift R G q LinearMap.id).2
  exact Representation.exists_intertwining_lift
    (moduleRepresentation R G V)
    (moduleRepresentation R G (V →₀ MonoidAlgebra R G))
    (moduleRepresentation R G V) hcard
    (moduleRepresentationMap R G q) (moduleRepresentationMap R G LinearMap.id) l hl

end MonoidAlgebra

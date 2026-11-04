/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.MonomialSubalgebra
public import GroupRings.MonoidAlgebra.MapDomainFinite
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite extensions of monomial subalgebras

For submonoids `S ≤ T` of a monoid, a finite left translate cover `T ⊆ S * E`
with `E ⊆ T` makes the `T`-monomial subalgebra a finite module over the
`S`-monomial subalgebra. Over a nontrivial coefficient semiring, the converse
holds. The module structure is induced by the inclusion of subalgebras.

These statements are consequences of the given-map criterion for monoid
algebras, applied to the exponent inclusion `S →* T`. The coefficient-preserving
monoid-algebra equivalences commute with inclusion, so the resulting module
structure is precisely the left inclusion action. The target exponent type
ensures that the finite set of remainders lies in `T`. Neither commutativity nor
cancellation of the exponent monoid is needed.

## References

* The polynomial-support, monoid-algebra supported-span, and finite-cover
  formalizations in ToricIdeals, by Formal Frontier Agents.
* Mathlib's finite-generation API, by Johan Commelin.
* Mathlib's monoid-algebra module and support API, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison.
* Mathlib's scalar-restriction API, by Nathaniel Thomas, Jeremy Avigad,
  Johannes Hölzl, and Mario Carneiro.
-/

@[expose] public section

namespace MonoidAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [Monoid M]

open scoped Pointwise

private theorem moduleFinite_monomialSubalgebra_iff_mapDomainRingHom
    {S T : Submonoid M} (hST : S ≤ T) :
    @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) ↔
    @Module.Finite R[S] R[T] _ _
      ((mapDomainRingHom R (Submonoid.inclusion hST)).toModule) := by
  let _ : Module (monomialSubalgebra R S) (monomialSubalgebra R T) :=
    (Subalgebra.inclusion (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule
  let _ : Module R[S] R[T] := (mapDomainRingHom R (Submonoid.inclusion hST)).toModule
  let eS := monomialSubalgebraEquiv R S
  let eT := monomialSubalgebraEquiv R T
  let _ : RingHomSurjective eS.toRingEquiv.toRingHom := ⟨eS.surjective⟩
  let F : R[T] →ₛₗ[eS.toRingEquiv.toRingHom] monomialSubalgebra R T :=
    { toFun := eT
      map_add' := eT.map_add
      map_smul' := fun a p => by
        change eT (mapDomainAlgHom R R (Submonoid.inclusion hST) a * p) =
          Subalgebra.inclusion (monomialSubalgebra_mono (R := R) hST) (eS a) * eT p
        rw [map_mul, monomialSubalgebraEquiv_mapDomain] }
  exact (F.finite_iff_of_bijective eT.bijective).symm

/-- A finite left translate cover of `T` by `S` makes the inclusion of their
monomial subalgebras module-finite. The coefficient semiring may be trivial. -/
theorem moduleFinite_monomialSubalgebra_of_subset_mul
    {S T : Submonoid M} (hST : S ≤ T) {E : Set M} (hE : E.Finite)
    (hET : E ⊆ (T : Set M)) (hcover : (T : Set M) ⊆ (S : Set M) * E) :
    @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) := by
  apply (moduleFinite_monomialSubalgebra_iff_mapDomainRingHom hST).2
  apply (moduleFinite_mapDomainRingHom_iff (R := R) (Submonoid.inclusion hST)).2
  refine Or.inl ⟨Subtype.val ⁻¹' E, hE.preimage Subtype.val_injective.injOn, ?_⟩
  intro t
  obtain ⟨s, hs, e, he, hse⟩ := hcover t.property
  exact ⟨⟨s, hs⟩, ⟨e, hET he⟩, he, Subtype.ext hse.symm⟩

/-- Over a nontrivial coefficient semiring, module finiteness of the inclusion
of monomial subalgebras gives a finite left translate cover of the exponent
submonoid. The remainders belong to the target submonoid. -/
theorem exists_finite_cover_of_moduleFinite_monomialSubalgebra [Nontrivial R]
    {S T : Submonoid M} (hST : S ≤ T)
    (hfinite : @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule)) :
    ∃ E : Set M, E.Finite ∧ E ⊆ (T : Set M) ∧
      (T : Set M) ⊆ (S : Set M) * E := by
  have hfinite' := (moduleFinite_monomialSubalgebra_iff_mapDomainRingHom hST).1 hfinite
  rcases (moduleFinite_mapDomainRingHom_iff (R := R) (Submonoid.inclusion hST)).1
      hfinite' with ⟨E, hE, hcover⟩ | hzero
  · refine ⟨Subtype.val '' E, hE.image _, ?_, ?_⟩
    · rintro _ ⟨t, _, rfl⟩
      exact t.property
    · intro t ht
      obtain ⟨s, e, he, hse⟩ := hcover ⟨t, ht⟩
      exact ⟨(s : M), s.property, (e : M), ⟨e, he, rfl⟩,
        (congrArg Subtype.val hse).symm⟩
  · let _ : Subsingleton R := hzero
    exact (zero_ne_one (Subsingleton.elim (0 : R) 1)).elim

/-- Over a nontrivial coefficient semiring, an inclusion of monomial
subalgebras is module-finite exactly when the target exponent submonoid has a
finite left translate cover by the source submonoid. -/
theorem moduleFinite_monomialSubalgebra_iff [Nontrivial R]
    {S T : Submonoid M} (hST : S ≤ T) :
    @Module.Finite (monomialSubalgebra R S) (monomialSubalgebra R T) _ _
      ((Subalgebra.inclusion
        (monomialSubalgebra_mono (R := R) hST)).toRingHom.toModule) ↔
    ∃ E : Set M, E.Finite ∧ E ⊆ (T : Set M) ∧
      (T : Set M) ⊆ (S : Set M) * E := by
  constructor
  · exact exists_finite_cover_of_moduleFinite_monomialSubalgebra hST
  · rintro ⟨E, hE, hET, hcover⟩
    exact moduleFinite_monomialSubalgebra_of_subset_mul hST hE hET hcover

end MonoidAlgebra

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Monomial spans for a homomorphism of monoid algebras

For a monoid homomorphism `f : M →* N`, give `R[N]` the left `R[M]`-module
structure obtained by restricting its regular action along
`MonoidAlgebra.mapDomainRingHom R f`. The span of the coefficient-one monomials
with labels in an arbitrary set `T` consists exactly of the elements whose
coefficient support lies in `Set.range f * T`.

The coefficient semiring and the exponent monoids need not be commutative.
No cancellation or nontriviality hypothesis is needed. In particular, the
support estimates used below are containments, so collisions of exponents and
vanishing products of coefficients cause no difficulty.

This characterization generalizes the monomial-subalgebra span argument in
`ToricIdeals.MonoidAlgebra.MonomialSubalgebra`, following its polynomial-support
predecessor in `ToricIdeals.MvPolynomial.MonomialSubalgebra`.

## References

* The polynomial-support and monoid-algebra monomial-span formalizations by
  Formal Frontier Agents.
* Mathlib's module restriction API, by Nathaniel Thomas, Jeremy Avigad,
  Johannes Hölzl, and Mario Carneiro.
* Mathlib's monoid-algebra and restricted-support API, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison, and its support estimates by Damiano Testa.
* Mathlib's span API, by Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
  Yury Kudryashov, Frédéric Dupuis, and Heather Macbeth.
-/

@[expose] public section

universe uR uM uN

open scoped Pointwise

namespace MonoidAlgebra

/-- For the left action restricted along `mapDomainRingHom R f`, the span of the
coefficient-one monomials labelled by `T` consists of the elements supported on
`Set.range f * T`. The set `T` is arbitrary, and the order of the factors records
the left scalar action. This generalizes the monomial-subalgebra span
characterization of Formal Frontier Agents. -/
theorem mem_span_single_mapDomainRingHom_iff
    {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [Monoid M] [Monoid N]
    (f : M →* N) (T : Set N) (p : MonoidAlgebra R N) :
    p ∈ @Submodule.span (MonoidAlgebra R M) (MonoidAlgebra R N)
      inferInstance inferInstance ((MonoidAlgebra.mapDomainRingHom R f).toModule)
      ((fun t : N => MonoidAlgebra.single t (1 : R)) '' T) ↔
      (↑p.coeff.support : Set N) ⊆ (Set.range f) * T := by
  classical
  let _ := (mapDomainRingHom R f).toModule
  constructor
  · intro hp
    have hp' : p ∈ supported R R ((Set.range f) * T) := by
      induction hp using Submodule.closure_induction with
      | zero => exact (supported R R _).zero_mem
      | add _ _ _ _ hx hy => exact (supported R R _).add_mem hx hy
      | smul_mem a x hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        apply mem_supported.mpr
        intro n hn
        rw [RingHom.toModule_smul (mapDomainRingHom R f)] at hn
        have hn' := support_coeff_mul_single_subset
          ((mapDomainRingHom R f) a) (1 : R) t hn
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn'
        have hk' : k ∈ (a.coeff.mapDomain f).support := by
          simpa [mapDomainRingHom, mapDomain] using hk
        obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk')
        exact ⟨f m, ⟨m, rfl⟩, t, ht, rfl⟩
    exact mem_supported.mp hp'
  · intro hp
    rw [← p.sum_coeff_single]
    apply Submodule.sum_mem
    intro n hn
    obtain ⟨a, ⟨m, rfl⟩, t, ht, rfl⟩ := hp hn
    have h := (Submodule.span (MonoidAlgebra R M)
      ((fun t : N => single t (1 : R)) '' T)).smul_mem
      (single m (p.coeff (f m * t))) (Submodule.subset_span ⟨t, ht, rfl⟩)
    simpa only [RingHom.toModule_smul (mapDomainRingHom R f),
      mapDomainRingHom_apply, mapDomain_single, single_mul_single, mul_one] using h

end MonoidAlgebra

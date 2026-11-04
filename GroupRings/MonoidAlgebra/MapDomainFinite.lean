/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.MapDomainSpan
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Set.Finite.Lattice

/-!
# Module finiteness along a monoid homomorphism

For a monoid homomorphism `f : M →* N`, the left regular module `R[N]`,
restricted along `mapDomainRingHom R f`, is finite if and only if either there
is a finite set `T` such that every target exponent has the form `f m * t`
with `t ∈ T`, or `R` is subsingleton. Coefficients may form a noncommutative
semiring, and the exponent monoids need not be commutative or cancellative.

A finite cover gives coefficient-one monomial generators through the
support-span characterization. Conversely, the union of the coefficient
supports of finitely many module generators is a finite remainder set.
Nontrivial coefficients let coefficient-one monomials detect every target
label. Subsingleton coefficients give a subsingleton target module.

## References

* The Formal Frontier polynomial-support, monoidal supported-span, and
  monomial finite-cover formalizations, for the support-union argument.
* Mathlib's finite-generation API, by Johan Commelin.
* Mathlib's monoid-algebra module and support API, by Johannes Hölzl,
  Yury Kudryashov, and Kim Morrison.
* Mathlib's restriction-of-scalars API, by Nathaniel Thomas, Jeremy Avigad,
  Johannes Hölzl, and Mario Carneiro.
-/

@[expose] public section

universe uR uM uN

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} {N : Type uN}
variable [Semiring R] [Monoid M] [Monoid N]

open scoped Pointwise

/-- A finite left translate cover of the target monoid makes its monoid
algebra finite over the source monoid algebra, for the left regular action
restricted along the given unchanged-coefficient homomorphism. The coefficient
semiring may be subsingleton. -/
theorem moduleFinite_mapDomainRingHom_of_finite_cover (f : M →* N)
    {T : Set N} (hT : T.Finite)
    (hcover : ∀ n : N, ∃ m : M, ∃ t ∈ T, n = f m * t) :
    @Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N)
      inferInstance inferInstance ((mapDomainRingHom R f).toModule) := by
  let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R N) :=
    (mapDomainRingHom R f).toModule
  have hspan : Submodule.span (MonoidAlgebra R M)
      ((fun t : N => single t (1 : R)) '' T) = ⊤ := by
    apply eq_top_iff.mpr
    intro p _
    apply (mem_span_single_mapDomainRingHom_iff f T p).mpr
    intro n _
    obtain ⟨m, t, ht, hn⟩ := hcover n
    exact ⟨f m, ⟨m, rfl⟩, t, ht, hn.symm⟩
  apply Module.Finite.of_fg_top
  rw [← hspan]
  exact Submodule.fg_span (hT.image _)

/-- Over a nontrivial coefficient semiring, finiteness of the target monoid
algebra for the restricted left regular action gives a finite left translate
cover of the target monoid by the image of the given monoid homomorphism. -/
theorem exists_finite_cover_of_moduleFinite_mapDomainRingHom [Nontrivial R]
    (f : M →* N)
    (hfinite : @Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N)
      inferInstance inferInstance ((mapDomainRingHom R f).toModule)) :
    ∃ T : Set N, T.Finite ∧ ∀ n : N, ∃ m : M, ∃ t ∈ T, n = f m * t := by
  classical
  let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R N) :=
    (mapDomainRingHom R f).toModule
  obtain ⟨G, hG, hspanG⟩ := Submodule.fg_def.mp hfinite.fg_top
  let T : Set N := ⋃ p ∈ G, (↑p.coeff.support : Set N)
  have hT : T.Finite := hG.biUnion fun p _ => p.coeff.support.finite_toSet
  refine ⟨T, hT, ?_⟩
  have hspanle : Submodule.span (MonoidAlgebra R M) G ≤
      Submodule.span (MonoidAlgebra R M)
        ((fun t : N => single t (1 : R)) '' T) := by
    apply Submodule.span_le.mpr
    intro p hp
    apply (mem_span_single_mapDomainRingHom_iff f T p).mpr
    intro n hn
    have hnT : n ∈ T := Set.mem_iUnion₂.mpr ⟨p, hp, hn⟩
    refine ⟨f 1, ⟨1, rfl⟩, n, hnT, ?_⟩
    simpa only [map_one] using (one_mul n)
  intro n
  have hntop : single n (1 : R) ∈
      (⊤ : Submodule (MonoidAlgebra R M) (MonoidAlgebra R N)) := Submodule.mem_top
  have hnspan : single n (1 : R) ∈ Submodule.span (MonoidAlgebra R M)
      ((fun t : N => single t (1 : R)) '' T) := hspanle (hspanG.symm ▸ hntop)
  have hn : n ∈ (Set.range f) * T := by
    apply (single_mem_span_single (R := R) (m := n) (s := (Set.range f) * T)).mp
    rw [← supported_eq_span_single]
    exact mem_supported.mpr ((mem_span_single_mapDomainRingHom_iff f T _).mp hnspan)
  obtain ⟨a, ⟨m, rfl⟩, t, ht, hmul⟩ := hn
  exact ⟨m, t, ht, hmul.symm⟩

/-- The target monoid algebra is finite for its left regular action restricted
along the given monoid-algebra homomorphism exactly when the target monoid has
a finite left translate cover by the image, or the coefficient semiring is
subsingleton. -/
theorem moduleFinite_mapDomainRingHom_iff
    {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [Monoid M] [Monoid N] (f : M →* N) :
    @Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N)
      inferInstance inferInstance ((MonoidAlgebra.mapDomainRingHom R f).toModule) ↔
      (∃ T : Set N, T.Finite ∧ ∀ n : N, ∃ m : M, ∃ t ∈ T, n = f m * t) ∨
        Subsingleton R := by
  constructor
  · intro hfinite
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · let _ : Nontrivial R := hR
      exact Or.inl (exists_finite_cover_of_moduleFinite_mapDomainRingHom f hfinite)
  · rintro (⟨T, hT, hcover⟩ | hR)
    · exact moduleFinite_mapDomainRingHom_of_finite_cover f hT hcover
    · let _ : Subsingleton R := hR
      let _ : Module (MonoidAlgebra R M) (MonoidAlgebra R N) :=
        (mapDomainRingHom R f).toModule
      infer_instance

/-- Over nontrivial coefficients, finiteness for the given restricted left
regular action is equivalent to a finite left translate cover of the target
monoid by the image of the monoid homomorphism. -/
theorem moduleFinite_mapDomainRingHom_iff_of_nontrivial [Nontrivial R]
    (f : M →* N) :
    @Module.Finite (MonoidAlgebra R M) (MonoidAlgebra R N)
      inferInstance inferInstance ((mapDomainRingHom R f).toModule) ↔
      ∃ T : Set N, T.Finite ∧ ∀ n : N, ∃ m : M, ∃ t ∈ T, n = f m * t := by
  constructor
  · intro hfinite
    rcases (moduleFinite_mapDomainRingHom_iff f).mp hfinite with hcover | hR
    · exact hcover
    · exact (zero_ne_one (hR.elim (0 : R) 1)).elim
  · intro hcover
    exact (moduleFinite_mapDomainRingHom_iff f).mpr (Or.inl hcover)

end MonoidAlgebra

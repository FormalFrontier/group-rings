/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.BinomialKernel
public import GroupRings.MonoidAlgebra.Noetherian

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coefficient-independent finite binomial generation

If the kernel of a monoid-algebra index map over the integers is finitely
generated, one finite set of same-fiber pairs generates the kernel over every
coefficient ring. For a finitely generated commutative source monoid, the
integer monoid algebra is Noetherian, so this conclusion holds without an
additional kernel hypothesis.

The finite set is chosen before the coefficient ring. Coefficients need not
commute, and `Ideal.span` denotes an ordinary left ideal. The source monoid,
target monoid, and coefficient ring have independent universes.

Finite extraction uses Mathlib's
`Submodule.fg_span_iff_fg_span_finset_subset` and
`Finset.subset_set_image_iff`. Coefficient change uses
`MonoidAlgebra.mapAlgHom` and `Ideal.map_span`.
-/

@[expose] public section

universe uR uN uM

namespace MonoidAlgebra

private theorem ker_mapDomainRingHom_eq_span_image_fiber
    (R : Type uR) {N : Type uN} {M : Type uM}
    [Ring R] [Monoid N] [Monoid M] (f : N →* M) :
    RingHom.ker (mapDomainRingHom R f) =
      Ideal.span
        ((fun ab : N × N =>
          (single ab.1 (1 : R) - single ab.2 (1 : R) : MonoidAlgebra R N)) ''
          {ab : N × N | f ab.1 = f ab.2}) := by
  rw [ker_mapDomainRingHom_eq_span_fiber R f]
  congr 1
  ext p
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨(a, b), hab, rfl⟩
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, b, hab, rfl⟩

private theorem uniform_fiber_span_of_integer_span_fg
    {N : Type uN} {M : Type uM} [Monoid N] [Monoid M] (f : N →* M)
    (hfg : (Ideal.span
      ((fun ab : N × N =>
        (single ab.1 (1 : ℤ) - single ab.2 (1 : ℤ) : MonoidAlgebra ℤ N)) ''
        {ab : N × N | f ab.1 = f ab.2})).FG) :
    ∃ E : Finset (N × N),
      (∀ ab ∈ E, f ab.1 = f ab.2) ∧
      ∀ (R : Type uR) [Ring R],
        RingHom.ker (mapDomainRingHom R f) =
          Ideal.span
            ((fun ab : N × N =>
              (single ab.1 (1 : R) - single ab.2 (1 : R) : MonoidAlgebra R N)) ''
              (↑E : Set (N × N))) := by
  classical
  let T : Set (N × N) := {ab | f ab.1 = f ab.2}
  let bZ : N × N → MonoidAlgebra ℤ N := fun ab =>
    single ab.1 (1 : ℤ) - single ab.2 (1 : ℤ)
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := MonoidAlgebra ℤ N) (bZ '' T)).mp hfg
  obtain ⟨E, hE, hEs⟩ := Finset.subset_set_image_iff.mp hs
  change Ideal.span (bZ '' T) = Ideal.span (s : Set (MonoidAlgebra ℤ N)) at hspan
  rw [← hEs, Finset.coe_image] at hspan
  refine ⟨E, ?_, ?_⟩
  · intro ab hab
    exact hE hab
  · intro R _
    let bR : N × N → MonoidAlgebra R N := fun ab =>
      single ab.1 (1 : R) - single ab.2 (1 : R)
    let c : MonoidAlgebra ℤ N →+* MonoidAlgebra R N :=
      (mapAlgHom N (Algebra.ofId ℤ R)).toRingHom
    have hc (ab : N × N) : c (bZ ab) = bR ab := by
      change mapAlgHom N (Algebra.ofId ℤ R)
          (single ab.1 (1 : ℤ) - single ab.2 (1 : ℤ)) =
        single ab.1 (1 : R) - single ab.2 (1 : R)
      simp only [map_sub, mapAlgHom_single, map_one]
    have hc_image (S : Set (N × N)) : c '' (bZ '' S) = bR '' S := by
      simp only [Set.image_image, hc]
    have hspanR : Ideal.span (bR '' T) =
        Ideal.span (bR '' (↑E : Set (N × N))) := by
      simpa only [Ideal.map_span, hc_image] using congrArg (Ideal.map c) hspan
    exact (ker_mapDomainRingHom_eq_span_image_fiber R f).trans hspanR

/-- Finite generation of the integer kernel gives one finite set of same-fiber
pairs whose unit-coefficient differences generate the kernel over every ring.
The coefficient ring need not be commutative, and generation is as a left ideal. -/
theorem uniform_fiber_span_of_integer_kernel_fg
    {N : Type uN} {M : Type uM} [Monoid N] [Monoid M] (f : N →* M)
    (hfg : (RingHom.ker (mapDomainRingHom ℤ f)).FG) :
    ∃ E : Finset (N × N),
      (∀ ab ∈ E, f ab.1 = f ab.2) ∧
      ∀ (R : Type uR) [Ring R],
        RingHom.ker (mapDomainRingHom R f) =
          Ideal.span
            ((fun ab : N × N =>
              (single ab.1 (1 : R) - single ab.2 (1 : R) : MonoidAlgebra R N)) ''
              (↑E : Set (N × N))) := by
  apply uniform_fiber_span_of_integer_span_fg f
  rw [← ker_mapDomainRingHom_eq_span_image_fiber ℤ f]
  exact hfg

/-- A finitely generated commutative source monoid admits one finite set of
same-fiber pairs whose unit-coefficient differences generate the kernel over
every ring. Neither the target monoid nor the coefficient ring need commute;
generation is as a left ideal. -/
theorem uniform_fiber_span_of_fg
    {N : Type uN} {M : Type uM} [CommMonoid N] [Monoid.FG N] [Monoid M]
    (f : N →* M) :
    ∃ E : Finset (N × N),
      (∀ ab ∈ E, f ab.1 = f ab.2) ∧
      ∀ (R : Type uR) [Ring R],
        RingHom.ker (mapDomainRingHom R f) =
          Ideal.span
            ((fun ab : N × N =>
              (single ab.1 (1 : R) - single ab.2 (1 : R) : MonoidAlgebra R N)) ''
              (↑E : Set (N × N))) := by
  let : IsNoetherianRing (MonoidAlgebra ℤ N) := isNoetherianRing_of_fg ℤ N
  exact uniform_fiber_span_of_integer_span_fg f (Ideal.fg_of_isNoetherianRing _)

end MonoidAlgebra

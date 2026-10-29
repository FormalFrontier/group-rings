/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coefficient ideals in monoid algebras

For every left ideal `I` of a semiring `R`, extension along the constants map
consists exactly of the elements whose coefficients lie in `I`. In particular,
coefficient change has kernel the extension of the coefficient kernel.
No commutativity, additive inverses or nontriviality is needed for this assertion.

For ring source coefficients and semiring target coefficients, the quotient by
this extended kernel is canonically the target algebra when the coefficient map
is surjective, and otherwise its range subsemiring. All basis coefficients are
preserved by the characteristic formulas.

## Implementation notes

The left-ideal expansion uses `single m 1 * single 1 r`, not a right ideal
closure argument. The quotient equivalences transport Mathlib's first
isomorphism theorem along the kernel equality.

## References

The maps, finite coefficient expansions, ideal extension and first-isomorphism
constructions are from Mathlib. The coefficient-ideal theorem generalizes the
polynomial results `Ideal.mem_map_C_iff` and `Polynomial.ker_mapRingHom`;
`GroupRings.Polynomial.CoefficientIdeals` gives their transport bridges.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

variable {R : Type u} {S : Type v} {M : Type w}

section AdditiveMap

variable [Semiring R] [Semiring S] [Nonempty M]

/-- A coefficientwise additive map on a nonempty index type is injective exactly
when its coefficient map is injective. No multiplicative index structure is needed. -/
theorem map_injective_iff (f : R →+ S) :
    Function.Injective (map (M := M) f) ↔ Function.Injective f := by
  classical
  constructor
  · intro h r s hrs
    let m : M := Classical.arbitrary M
    apply single_right_injective (m := m)
    apply h
    simp only [map_single, hrs]
  · exact map_injective f

/-- A coefficientwise additive map on a nonempty index type is surjective exactly
when its coefficient map is surjective. Empty index types would invalidate reflection. -/
theorem map_surjective_iff (f : R →+ S) :
    Function.Surjective (map (M := M) f) ↔ Function.Surjective f := by
  classical
  constructor
  · intro h s
    let m : M := Classical.arbitrary M
    obtain ⟨x, hx⟩ := h (single m s)
    refine ⟨x.coeff m, ?_⟩
    simpa using congrArg (fun y : S[M] => y.coeff m) hx
  · exact map_surjective f

end AdditiveMap

section Semiring

variable [Semiring R] [Semiring S] [Monoid M]

/-- Extension of any ordinary left coefficient ideal consists exactly of the
elements whose coefficients belong to that ideal. -/
theorem mem_map_singleOneRingHom_iff (I : Ideal R) (x : R[M]) :
    x ∈ Ideal.map (singleOneRingHom (M := M)) I ↔ ∀ m, x.coeff m ∈ I := by
  classical
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨r, hr, rfl⟩ m
      by_cases hm : (1 : M) = m
      · simpa [hm] using hr
      · simp [singleOneRingHom_apply, hm]
    · intro m
      simp
    · intro x y _ _ hx hy m
      simpa only [coeff_add, Finsupp.add_apply] using I.add_mem (hx m) (hy m)
    · intro x y _ hy m
      simp only [smul_eq_mul, coeff_mul, Finsupp.sum]
      exact I.sum_mem fun a _ => I.sum_mem fun b _ =>
        by split_ifs <;> first | exact I.mul_mem_left _ (hy b) | exact I.zero_mem
  · intro hx
    rw [← sum_coeff_single x, Finsupp.sum]
    apply (Ideal.map (singleOneRingHom (M := M)) I).sum_mem
    intro m _
    have h := (Ideal.map (singleOneRingHom (M := M)) I).mul_mem_left
      (single m 1) (Ideal.mem_map_of_mem (singleOneRingHom (M := M)) (hx m))
    change single m 1 * single 1 (x.coeff m) ∈ _ at h
    simpa only [single_mul_single, mul_one, one_mul] using h

/-- Membership of a single term in an extended coefficient ideal detects its
coefficient, at every index. -/
@[simp] theorem single_mem_map_singleOneRingHom_iff (I : Ideal R) (m : M) (r : R) :
    single m r ∈ Ideal.map (singleOneRingHom (M := M)) I ↔ r ∈ I := by
  classical
  rw [mem_map_singleOneRingHom_iff]
  constructor
  · intro h
    simpa using h m
  · intro h n
    by_cases hn : m = n
    · simpa [hn] using h
    · simp [hn]

/-- The kernel of coefficient change is the ordinary left ideal extended from
the coefficient kernel, over arbitrary semirings. -/
theorem ker_mapRingHom (f : R →+* S) :
    RingHom.ker (mapRingHom M f) =
      Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f) := by
  ext x
  rw [mem_map_singleOneRingHom_iff, RingHom.mem_ker, ← coeff_inj, Finsupp.ext_iff]
  simp only [coeff_mapRingHom, coeff_zero, Finsupp.zero_apply, RingHom.mem_ker]

/-- Coefficient change vanishes exactly when every original coefficient belongs
to the coefficient kernel. This does not describe index-map collisions. -/
theorem mapRingHom_eq_zero_iff (f : R →+* S) (x : R[M]) :
    mapRingHom M f x = 0 ↔ ∀ m, x.coeff m ∈ RingHom.ker f := by
  rw [← RingHom.mem_ker, ker_mapRingHom, mem_map_singleOneRingHom_iff]

/-- The extension of the coefficient kernel is two-sided, as the kernel of the
coefficient-change homomorphism. -/
instance map_singleOneRingHom_ker_isTwoSided (f : R →+* S) :
    (Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f)).IsTwoSided :=
  ker_mapRingHom (M := M) f ▸ inferInstance

end Semiring

section Ring

variable [Ring R] [Semiring S] [Monoid M]

noncomputable section

/-- Surjective coefficient change identifies the quotient by the extended
coefficient kernel with the target monoid algebra. The target needs only a semiring. -/
def quotientCoeffKerEquiv (f : R →+* S) (hf : Function.Surjective f) :
    (R[M] ⧸ Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f)) ≃+* S[M] :=
  (Ideal.quotEquivOfEq (ker_mapRingHom f).symm).trans
    (RingHom.quotientKerEquivOfSurjective (map_surjective f.toAddMonoidHom hf))

/-- On every quotient class the coefficient quotient equivalence is coefficient change. -/
@[simp] theorem quotientCoeffKerEquiv_mk (f : R →+* S) (hf : Function.Surjective f)
    (x : R[M]) :
    quotientCoeffKerEquiv f hf (Ideal.Quotient.mk _ x) = mapRingHom M f x := by
  rfl

/-- Every basis coefficient is preserved by the coefficient quotient equivalence. -/
theorem quotientCoeffKerEquiv_mk_single (f : R →+* S) (hf : Function.Surjective f)
    (m : M) (r : R) :
    quotientCoeffKerEquiv f hf (Ideal.Quotient.mk _ (single m r)) = single m (f r) := by
  simp

/-- Values on quotient classes uniquely characterize the coefficient quotient equivalence. -/
theorem quotientCoeffKerEquiv_unique (f : R →+* S) (hf : Function.Surjective f)
    (e : (R[M] ⧸ Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f)) ≃+* S[M])
    (h : ∀ x, e (Ideal.Quotient.mk _ x) = mapRingHom M f x) :
    e = quotientCoeffKerEquiv f hf := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (h x).trans (quotientCoeffKerEquiv_mk f hf x).symm

/-- Without surjectivity, the quotient by the extended coefficient kernel is
the range subsemiring of coefficient change, not necessarily the whole target. -/
def quotientCoeffKerEquivRange (f : R →+* S) :
    (R[M] ⧸ Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f)) ≃+*
      (mapRingHom M f).rangeS :=
  (Ideal.quotEquivOfEq (ker_mapRingHom f).symm).trans
    (RingHom.quotientKerEquivRangeS (mapRingHom M f))

/-- The range equivalence sends a quotient class to its coefficient-change image. -/
@[simp] theorem quotientCoeffKerEquivRange_mk (f : R →+* S) (x : R[M]) :
    (quotientCoeffKerEquivRange f (Ideal.Quotient.mk _ x) : S[M]) =
      mapRingHom M f x := by
  rfl

/-- The range equivalence retains every single-term coefficient. -/
theorem quotientCoeffKerEquivRange_mk_single (f : R →+* S) (m : M) (r : R) :
    (quotientCoeffKerEquivRange f (Ideal.Quotient.mk _ (single m r)) : S[M]) =
      single m (f r) := by
  simp

/-- The class formula characterizes the range equivalence uniquely. -/
theorem quotientCoeffKerEquivRange_unique (f : R →+* S)
    (e : (R[M] ⧸ Ideal.map (singleOneRingHom (M := M)) (RingHom.ker f)) ≃+*
      (mapRingHom M f).rangeS)
    (h : ∀ x, (e (Ideal.Quotient.mk _ x) : S[M]) = mapRingHom M f x) :
    e = quotientCoeffKerEquivRange f := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Subtype.ext
  exact (h x).trans (quotientCoeffKerEquivRange_mk f x).symm

end

end Ring

end MonoidAlgebra

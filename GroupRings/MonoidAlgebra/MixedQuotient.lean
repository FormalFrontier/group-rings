/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.CoefficientIdeals
public import GroupRings.MonoidAlgebra.KernelRange

/-!
# Simultaneous coefficient and index quotients

For `f : R →+* S` and `φ : G →* M`, with `R` a ring, `S` a semiring,
`G` a group and `M` any monoid, the kernel of simultaneous coefficient and
index change is the sum of the subgroup-difference ideal and the extension
of `ker f`. Neither map need be surjective. Collisions of indices may cancel;
this kernel is not asserted to be coefficientwise in `ker f`.

When `f` is surjective the quotient is `S[MonoidHom.mrange φ]`. If `φ` is
also surjective it is `S[M]`. For arbitrary maps the unconditional target is
the range subsemiring of the composite. All four type universes are independent.

## Implementation notes

The proof factors through the surjective index map with coefficients still in
`R`. Ideal extension-contraction is applied between rings, before coefficient
change to `S`; no ring structure on `S` is imposed. The final range inclusion
is injective on unchanged coefficients.

## References

This combines the coefficient-ideal membership theorem with the group-to-monoid
kernel theorem in `GroupRings.MonoidAlgebra.KernelRange`, using Mathlib's
coefficient/index naturality, ideal extension-contraction and first isomorphism
constructions. No new map or ideal factory is introduced.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace MonoidAlgebra

variable {R : Type u} {S : Type v} {G : Type w} {M : Type z}
variable [Ring R] [Semiring S] [Group G] [Monoid M]

private theorem ker_coeff_comp_index_surjective {N : Type*} [Monoid N]
    (f : R →+* S) (φ : G →* N) (hφ : Function.Surjective φ) :
    RingHom.ker ((mapRingHom N f).comp (mapDomainRingHom R φ)) =
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f) ⊔
        RingHom.ker (mapDomainRingHom R φ) := by
  rw [← RingHom.comap_ker, ker_mapRingHom]
  have hc : (mapDomainRingHom R φ).comp (singleOneRingHom (M := G)) =
      singleOneRingHom (M := N) := by
    ext r
    simp [singleOneRingHom_apply, mapDomain_single]
  rw [← hc, ← Ideal.map_map]
  exact Ideal.comap_map_of_surjective' (mapDomainRingHom R φ)
    (mapDomainRingHom_surjective R G φ hφ) _

private theorem ker_coeff_comp_mrange (f : R →+* S) (φ : G →* M) :
    RingHom.ker ((mapRingHom (MonoidHom.mrange φ) f).comp
      (mapDomainRingHom R φ.mrangeRestrict)) =
      Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
        Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f) := by
  have hker : φ.mrangeRestrict.ker = φ.ker := by
    ext g
    change φ.mrangeRestrict g = 1 ↔ φ g = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [ker_coeff_comp_index_surjective f φ.mrangeRestrict φ.mrangeRestrict_surjective,
    ker_mapDomainRingHom, hker, sup_comm]

/-- The simultaneous coefficient/index kernel is the sum of the index-kernel
relations and the extended coefficient kernel. No surjectivity or nontriviality
is required, and the target index monoid need not be cancellative or a group. -/
theorem ker_mapDomainRingHom_comp_mapRingHom (f : R →+* S) (φ : G →* M) :
    RingHom.ker ((mapDomainRingHom S φ).comp (mapRingHom G f)) =
      Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
        Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f) := by
  let i := mapDomainRingHom S (MonoidHom.mrange φ).subtype
  have hi : Function.Injective i := mapDomain_injective Subtype.val_injective
  have hfactor : (mapDomainRingHom S φ).comp (mapRingHom G f) =
      i.comp ((mapRingHom (MonoidHom.mrange φ) f).comp
        (mapDomainRingHom R φ.mrangeRestrict)) := by
    rw [mapRingHom_comp_mapDomainRingHom, ← RingHom.comp_assoc,
      ← mapDomainRingHom_comp]
    rfl
  rw [hfactor, ← ker_coeff_comp_mrange f φ]
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  exact ⟨fun h => hi (h.trans (map_zero i).symm), fun h => h ▸ map_zero i⟩

/-- The sum ideal in the mixed kernel theorem is two-sided because it is the
kernel of the simultaneous homomorphism. -/
instance mixedCoeffKer_isTwoSided (f : R →+* S) (φ : G →* M) :
    (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f)).IsTwoSided :=
  ker_mapDomainRingHom_comp_mapRingHom f φ ▸ inferInstance

/-- With surjective coefficients, quotient by both kinds of relation is the
monoid algebra of the range of the index map. -/
def quotientMixedKerEquivMrange (f : R →+* S) (hf : Function.Surjective f) (φ : G →* M) :
    (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+*
        S[MonoidHom.mrange φ] :=
  (Ideal.quotEquivOfEq (J := RingHom.ker ((mapRingHom (MonoidHom.mrange φ) f).comp
      (mapDomainRingHom R φ.mrangeRestrict))) (by
        exact (ker_coeff_comp_mrange f φ).symm)).trans
    (RingHom.quotientKerEquivOfSurjective
      ((map_surjective f.toAddMonoidHom hf).comp
        (mapDomainRingHom_surjective R G φ.mrangeRestrict φ.mrangeRestrict_surjective)))

/-- On every class, the mixed range-index equivalence first pushes indices to
the range and then changes coefficients. -/
@[simp] theorem quotientMixedKerEquivMrange_mk (f : R →+* S) (hf : Function.Surjective f)
    (φ : G →* M) (x : R[G]) :
    quotientMixedKerEquivMrange f hf φ (Ideal.Quotient.mk _ x) =
      mapRingHom (MonoidHom.mrange φ) f (mapDomainRingHom R φ.mrangeRestrict x) := by
  rfl

/-- The mixed range-index equivalence preserves every basis coefficient. -/
theorem quotientMixedKerEquivMrange_mk_single (f : R →+* S) (hf : Function.Surjective f)
    (φ : G →* M) (g : G) (r : R) :
    quotientMixedKerEquivMrange f hf φ (Ideal.Quotient.mk _ (single g r)) =
      single (φ.mrangeRestrict g) (f r) := by
  simp [mapDomain_single]

/-- The class formula uniquely characterizes the mixed range-index equivalence. -/
theorem quotientMixedKerEquivMrange_unique (f : R →+* S) (hf : Function.Surjective f)
    (φ : G →* M)
    (e : (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+*
        S[MonoidHom.mrange φ])
    (h : ∀ x, e (Ideal.Quotient.mk _ x) =
      mapRingHom (MonoidHom.mrange φ) f (mapDomainRingHom R φ.mrangeRestrict x)) :
    e = quotientMixedKerEquivMrange f hf φ := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (h x).trans (quotientMixedKerEquivMrange_mk f hf φ x).symm

/-- If both maps are surjective, the simultaneous quotient is the whole target
monoid algebra. Surjectivity of the index map is sufficient, not necessary. -/
def quotientMixedKerEquivOfSurjective (f : R →+* S) (hf : Function.Surjective f)
    (φ : G →* M) (hφ : Function.Surjective φ) :
    (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+* S[M] :=
  (Ideal.quotEquivOfEq (ker_mapDomainRingHom_comp_mapRingHom f φ).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((mapDomainRingHom_surjective S G φ hφ).comp (map_surjective f.toAddMonoidHom hf)))

/-- The full-target equivalence is the simultaneous map on all classes. -/
@[simp] theorem quotientMixedKerEquivOfSurjective_mk (f : R →+* S)
    (hf : Function.Surjective f) (φ : G →* M) (hφ : Function.Surjective φ) (x : R[G]) :
    quotientMixedKerEquivOfSurjective f hf φ hφ (Ideal.Quotient.mk _ x) =
      mapDomainRingHom S φ (mapRingHom G f x) := by
  rfl

/-- All original basis coefficients have their expected simultaneous images. -/
theorem quotientMixedKerEquivOfSurjective_mk_single (f : R →+* S)
    (hf : Function.Surjective f) (φ : G →* M) (hφ : Function.Surjective φ) (g : G) (r : R) :
    quotientMixedKerEquivOfSurjective f hf φ hφ (Ideal.Quotient.mk _ (single g r)) =
      single (φ g) (f r) := by
  simp [mapDomain_single]

/-- The full-target equivalence is unique with its formula on all classes. -/
theorem quotientMixedKerEquivOfSurjective_unique (f : R →+* S)
    (hf : Function.Surjective f) (φ : G →* M) (hφ : Function.Surjective φ)
    (e : (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+* S[M])
    (h : ∀ x, e (Ideal.Quotient.mk _ x) = mapDomainRingHom S φ (mapRingHom G f x)) :
    e = quotientMixedKerEquivOfSurjective f hf φ hφ := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (h x).trans (quotientMixedKerEquivOfSurjective_mk f hf φ hφ x).symm

/-- Without surjectivity, quotient by the mixed kernel is the range subsemiring
of the simultaneous map. -/
def quotientMixedKerEquivRange (f : R →+* S) (φ : G →* M) :
    (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+*
        ((mapDomainRingHom S φ).comp (mapRingHom G f)).rangeS :=
  (Ideal.quotEquivOfEq (ker_mapDomainRingHom_comp_mapRingHom f φ).symm).trans
    (RingHom.quotientKerEquivRangeS ((mapDomainRingHom S φ).comp (mapRingHom G f)))

/-- The unconditional range equivalence is the simultaneous map on classes. -/
@[simp] theorem quotientMixedKerEquivRange_mk (f : R →+* S) (φ : G →* M) (x : R[G]) :
    (quotientMixedKerEquivRange f φ (Ideal.Quotient.mk _ x) : S[M]) =
      mapDomainRingHom S φ (mapRingHom G f x) := by
  rfl

/-- The unconditional range equivalence retains every basis coefficient. -/
theorem quotientMixedKerEquivRange_mk_single (f : R →+* S) (φ : G →* M) (g : G) (r : R) :
    (quotientMixedKerEquivRange f φ (Ideal.Quotient.mk _ (single g r)) : S[M]) =
      single (φ g) (f r) := by
  simp [mapDomain_single]

/-- Values on all classes uniquely characterize the unconditional range equivalence. -/
theorem quotientMixedKerEquivRange_unique (f : R →+* S) (φ : G →* M)
    (e : (R[G] ⧸ (Ideal.span (Set.range fun n : φ.ker => single (n : G) (1 : R) - 1) ⊔
      Ideal.map (singleOneRingHom (M := G)) (RingHom.ker f))) ≃+*
        ((mapDomainRingHom S φ).comp (mapRingHom G f)).rangeS)
    (h : ∀ x, (e (Ideal.Quotient.mk _ x) : S[M]) =
      mapDomainRingHom S φ (mapRingHom G f x)) :
    e = quotientMixedKerEquivRange f φ := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Subtype.ext
  exact (h x).trans (quotientMixedKerEquivRange_mk f φ x).symm

end MonoidAlgebra

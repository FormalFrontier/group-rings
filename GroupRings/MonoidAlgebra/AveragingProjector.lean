/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.ModuleRepresentationEquiv
public import GroupTheory.RepresentationAveragingProjector

/-!
# Normalized norm on a given group-algebra module

The representation self-intertwiner transports to a linear endomorphism of the
original module through `moduleRepresentationMapEquiv`. No replacement module
or independently specified group action is needed.

The mean is an idempotent, fixes exactly the vectors fixed by the canonical
group symbols, and has range their full group-algebra span. It is natural for
all linear maps between the original group-algebra modules.

## References

This construction uses the normalized representation norm and the correspondence
between original monoid-algebra module maps and coefficient-linear intertwiners.
-/

@[expose] public section

noncomputable section

universe uR uG uV uW

namespace MonoidAlgebra

variable (R : Type uR) (G : Type uG) (V : Type uV)
variable [Semiring R] [Group G] [Finite G] [AddCommMonoid V]
variable [Module (MonoidAlgebra R G) V]

/-- The normalized norm on the given group-algebra module, linear over the full
monoid algebra. -/
def averagingProjector (h : IsUnit (Nat.card G : R)) :
    Module.End (MonoidAlgebra R G) V := by
  letI : Module R V := moduleCoefficientModule R G V
  exact (moduleRepresentationMapEquiv R G).symm
    (Representation.averagingProjector (moduleRepresentation R G V) h)

/-- Transporting the self-intertwiner does not change its value on a vector. -/
theorem averagingProjector_apply (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector R G V h v =
      @Representation.averagingProjector R G V _ _ _ _
        (moduleCoefficientModule R G V) (moduleRepresentation R G V) h v := rfl

/-- The canonical representation of the mean is the generic self-intertwiner. -/
@[simp]
theorem moduleRepresentationMap_averagingProjector (h : IsUnit (Nat.card G : R)) :
    moduleRepresentationMap R G (averagingProjector R G V h) =
      @Representation.averagingProjector R G V _ _ _ _
        (moduleCoefficientModule R G V) (moduleRepresentation R G V) h := by
  let : Module R V := moduleCoefficientModule R G V
  ext v
  rfl

/-- Restricting the mean to the canonical coefficient action, by the
coefficient-linear map of `moduleRepresentationMap`, recovers the generic mean. -/
theorem averagingProjector_coefficientMap (h : IsUnit (Nat.card G : R)) :
    @Representation.IntertwiningMap.toLinearMap R G V V _ _ _ _
        (moduleCoefficientModule R G V) (moduleCoefficientModule R G V) _ _
        (moduleRepresentationMap R G (averagingProjector R G V h)) =
      @Representation.IntertwiningMap.toLinearMap R G V V _ _ _ _
        (moduleCoefficientModule R G V) (moduleCoefficientModule R G V) _ _
        (@Representation.averagingProjector R G V _ _ _ _
          (moduleCoefficientModule R G V) (moduleRepresentation R G V) h) := by
  rw [moduleRepresentationMap_averagingProjector]

/-- Every coefficient unit representing the order gives this same endomorphism
on the given module. Only `Finite` is required. -/
theorem averagingProjector_apply_eq_sum (h : IsUnit (Nat.card G : R))
    (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (v : V) :
    averagingProjector R G V h v =
      (single 1 (↑u⁻¹ : R) : MonoidAlgebra R G) •
        ∑ g ∈ @Finset.univ G (Fintype.ofFinite G),
          (single g (1 : R) : MonoidAlgebra R G) • v := by
  let : Module R V := moduleCoefficientModule R G V
  rw [averagingProjector_apply,
    Representation.averagingProjector_apply_eq_sum _ h u hu]
  rfl

/-- Any supplied `Fintype` computes the same mean; the principal constructor
requires no such data. -/
theorem averagingProjector_apply_eq_sum_fintype [Fintype G]
    (h : IsUnit (Nat.card G : R)) (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (v : V) :
    averagingProjector R G V h v =
      (single 1 (↑u⁻¹ : R) : MonoidAlgebra R G) •
        ∑ g : G, (single g (1 : R) : MonoidAlgebra R G) • v := by
  rw [averagingProjector_apply_eq_sum R G V h u hu]
  rw [show Fintype.ofFinite G = (inferInstance : Fintype G) from Subsingleton.elim _ _]

/-- The mean is independent of the proof that the order is a unit. -/
theorem averagingProjector_eq (h h' : IsUnit (Nat.card G : R)) :
    averagingProjector R G V h = averagingProjector R G V h' := by
  ext v
  rfl

/-- Every mean is fixed by every canonical group symbol. -/
@[simp]
theorem single_smul_averagingProjector (h : IsUnit (Nat.card G : R)) (g : G) (v : V) :
    (single g (1 : R) : MonoidAlgebra R G) • averagingProjector R G V h v =
      averagingProjector R G V h v := by
  let : Module R V := moduleCoefficientModule R G V
  rw [averagingProjector_apply]
  exact (Representation.mem_fixedSubmodule _ _).1
    (Representation.averagingProjector_mem_fixedSubmodule (moduleRepresentation R G V) h v) g

/-- The mean fixes every vector fixed by the canonical group symbols. -/
theorem averagingProjector_eq_self (h : IsUnit (Nat.card G : R)) {v : V}
    (hv : ∀ g : G, (single g (1 : R) : MonoidAlgebra R G) • v = v) :
    averagingProjector R G V h v = v := by
  let : Module R V := moduleCoefficientModule R G V
  rw [averagingProjector_apply]
  exact Representation.averagingProjector_eq_self _ h
    ((Representation.mem_fixedSubmodule _ _).2 hv)

/-- Exactly the fixed vectors are unchanged by averaging. -/
@[simp]
theorem averagingProjector_eq_self_iff (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector R G V h v = v ↔
      ∀ g : G, (single g (1 : R) : MonoidAlgebra R G) • v = v := by
  constructor
  · intro hv g
    rw [← hv]
    exact single_smul_averagingProjector R G V h g v
  · exact averagingProjector_eq_self R G V h

/-- The mean is idempotent on vectors. -/
@[simp]
theorem averagingProjector_apply_apply (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector R G V h (averagingProjector R G V h v) =
      averagingProjector R G V h v :=
  averagingProjector_eq_self R G V h (fun g => single_smul_averagingProjector R G V h g v)

/-- The mean is an idempotent endomorphism of the original group-algebra module. -/
@[simp]
theorem averagingProjector_comp_self (h : IsUnit (Nat.card G : R)) :
    (averagingProjector R G V h).comp (averagingProjector R G V h) =
      averagingProjector R G V h := by
  ext v
  exact averagingProjector_apply_apply R G V h v

/-- Membership in the full group-algebra range is precisely fixedness. -/
theorem mem_range_averagingProjector (h : IsUnit (Nat.card G : R)) (v : V) :
    v ∈ (averagingProjector R G V h).range ↔
      ∀ g : G, (single g (1 : R) : MonoidAlgebra R G) • v = v := by
  constructor
  · rintro ⟨w, rfl⟩ g
    exact single_smul_averagingProjector R G V h g w
  · intro hv
    exact ⟨v, averagingProjector_eq_self R G V h hv⟩

/-- The full group-algebra range is the group-algebra span of all fixed vectors.
No separate fixed-space object is introduced. -/
theorem range_averagingProjector (h : IsUnit (Nat.card G : R)) :
    (averagingProjector R G V h).range =
      Submodule.span (MonoidAlgebra R G)
        {v : V | ∀ g : G, (single g (1 : R) : MonoidAlgebra R G) • v = v} := by
  apply le_antisymm
  · intro v hv
    exact Submodule.subset_span ((mem_range_averagingProjector R G V h v).1 hv)
  · apply Submodule.span_le.mpr
    intro v hv
    exact (mem_range_averagingProjector R G V h v).2 hv

variable {V}
variable {W : Type uW} [AddCommMonoid W] [Module (MonoidAlgebra R G) W]

/-- Every linear map between the original group-algebra modules commutes with
the means, by the existing norm naturality for its canonical intertwiner. -/
theorem averagingProjector_comm_apply (f : V →ₗ[MonoidAlgebra R G] W)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    f (averagingProjector R G V h v) = averagingProjector R G W h (f v) := by
  let : Module R V := moduleCoefficientModule R G V
  let : Module R W := moduleCoefficientModule R G W
  exact (moduleRepresentationMap R G f).averagingProjector_comm_apply h v

/-- Naturality as equality of original group-algebra linear maps. -/
theorem averagingProjector_comm (f : V →ₗ[MonoidAlgebra R G] W)
    (h : IsUnit (Nat.card G : R)) :
    f.comp (averagingProjector R G V h) = (averagingProjector R G W h).comp f := by
  ext v
  exact averagingProjector_comm_apply R G f h v

/-- Among original group-algebra endomorphisms, the mean is the unique
retraction onto the fixed vectors. This does not claim uniqueness among
arbitrary coefficient-linear retractions. -/
theorem eq_averagingProjector (h : IsUnit (Nat.card G : R))
    (p : Module.End (MonoidAlgebra R G) V)
    (hp : ∀ v g, (single g (1 : R) : MonoidAlgebra R G) • p v = p v)
    (hfix : ∀ v, (∀ g : G, (single g (1 : R) : MonoidAlgebra R G) • v = v) → p v = v) :
    p = averagingProjector R G V h := by
  let : Module R V := moduleCoefficientModule R G V
  apply moduleRepresentationMap_injective R G
  rw [moduleRepresentationMap_averagingProjector]
  exact Representation.eq_averagingProjector (moduleRepresentation R G V) h
    (moduleRepresentationMap R G p)
    (fun v => (Representation.mem_fixedSubmodule _ _).2 (hp v))
    (fun v hv => hfix v ((Representation.mem_fixedSubmodule _ _).1 hv))

end MonoidAlgebra

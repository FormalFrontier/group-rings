/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.ModuleRepresentation
public import GroupRings.MonoidAlgebra.ModuleMaps

/-!
# Intertwiners between given monoid-algebra modules

The canonical representation identifies original monoid-algebra linear maps
with coefficient-linear intertwiners, without changing their values. The
identification is additive over arbitrary semirings; it does not require a
pointwise scalar module structure on spaces of linear maps.

This equivalence reflects the existence of lifts between the original modules.
For commutative coefficients its inverse agrees with Mathlib's Hom correspondence
after the canonical type-synonym equivalences.

## References

Mathlib's `Representation.IntertwiningMap.equivLinearMapAsModule` identifies
intertwiners with monoid-algebra linear maps on representation-module type synonyms
over commutative semirings. The additive correspondence here retains the original
given modules and allows noncommutative coefficients. Its commutative comparison
uses `Representation.asModuleEquiv`.
-/

@[expose] public section

noncomputable section

universe uR uM uV uW uX

namespace MonoidAlgebra

section Semiring

variable (R : Type uR) (M : Type uM) [Semiring R] [Monoid M]
variable {V : Type uV} [AddCommMonoid V] [Module (MonoidAlgebra R M) V]
variable {W : Type uW} [AddCommMonoid W] [Module (MonoidAlgebra R M) W]
variable {X : Type uX} [AddCommMonoid X] [Module (MonoidAlgebra R M) X]

/-- Original monoid-algebra linear maps are additively equivalent to
intertwiners between the canonical representations on the same modules. -/
def moduleRepresentationMapEquiv :
    letI : Module R V := moduleCoefficientModule R M V
    letI : Module R W := moduleCoefficientModule R M W
    (V →ₗ[MonoidAlgebra R M] W) ≃+
      Representation.IntertwiningMap (moduleRepresentation R M V) (moduleRepresentation R M W) := by
  letI : Module R V := moduleCoefficientModule R M V
  letI : Module R W := moduleCoefficientModule R M W
  exact
    { toFun := moduleRepresentationMap R M
      invFun := fun F =>
        { toFun := F
          map_add' := F.map_add
          map_smul' := (map_smul_iff_coefficient_basis F.toLinearMap.toAddMonoidHom).2
            ⟨fun r v => F.map_smul r v,
              fun m v => Representation.IntertwiningMap.isIntertwining _ _ F m v⟩ }
      left_inv := fun f => by ext v; rfl
      right_inv := fun F => by ext v; rfl
      map_add' := fun f g => by ext v; rfl }

/-- The additive equivalence extends the canonical packaging of linear maps. -/
@[simp]
theorem moduleRepresentationMapEquiv_apply (f : V →ₗ[MonoidAlgebra R M] W) :
    moduleRepresentationMapEquiv R M f = moduleRepresentationMap R M f := rfl

/-- Recovering an original linear map from a canonical intertwiner preserves
its value on every vector. -/
@[simp]
theorem moduleRepresentationMapEquiv_symm_apply
    (F : @Representation.IntertwiningMap R M V W _ _ _ _
      (moduleCoefficientModule R M V) (moduleCoefficientModule R M W)
      (moduleRepresentation R M V) (moduleRepresentation R M W)) (v : V) :
    (moduleRepresentationMapEquiv R M).symm F v = F v := rfl

/-- A lift between original monoid-algebra maps exists precisely when a lift
between their canonical intertwiners exists. -/
theorem exists_linear_lift_iff_exists_intertwining_lift
    (q : W →ₗ[MonoidAlgebra R M] X) (h : V →ₗ[MonoidAlgebra R M] X) :
    (∃ f : V →ₗ[MonoidAlgebra R M] W, q.comp f = h) ↔
      ∃ f : @Representation.IntertwiningMap R M V W _ _ _ _
          (moduleCoefficientModule R M V) (moduleCoefficientModule R M W)
          (moduleRepresentation R M V) (moduleRepresentation R M W),
        @Representation.IntertwiningMap.comp R M V W X _ _ _ _ _
            (moduleCoefficientModule R M V) (moduleCoefficientModule R M W)
            (moduleCoefficientModule R M X)
            (moduleRepresentation R M V) (moduleRepresentation R M W)
            (moduleRepresentation R M X) (moduleRepresentationMap R M q) f =
          moduleRepresentationMap R M h := by
  let : Module R V := moduleCoefficientModule R M V
  let : Module R W := moduleCoefficientModule R M W
  let : Module R X := moduleCoefficientModule R M X
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨moduleRepresentationMap R M f, ?_⟩
    rw [← moduleRepresentationMap_comp, hf]
  · rintro ⟨F, hF⟩
    refine ⟨(moduleRepresentationMapEquiv R M).symm F, ?_⟩
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.comp_apply, moduleRepresentationMapEquiv_symm_apply,
      Representation.IntertwiningMap.comp_apply, moduleRepresentationMap_apply] using
      congrArg (fun k => k v) hF

end Semiring

section CommSemiring

variable (R : Type uR) (M : Type uM) [CommSemiring R] [Monoid M]
variable {V : Type uV} [AddCommMonoid V] [Module (MonoidAlgebra R M) V]
variable {W : Type uW} [AddCommMonoid W] [Module (MonoidAlgebra R M) W]

/-- Under commutative coefficients the inverse correspondence agrees with
Mathlib's Hom equivalence after the canonical `asModuleEquiv` transports. -/
theorem moduleRepresentationMapEquiv_symm_asModule_apply
    (F : @Representation.IntertwiningMap R M V W _ _ _ _
      (moduleCoefficientModule R M V) (moduleCoefficientModule R M W)
      (moduleRepresentation R M V) (moduleRepresentation R M W))
    (x : @Representation.asModule R M V _ _ _
      (moduleCoefficientModule R M V) (moduleRepresentation R M V)) :
    @Representation.asModuleEquiv R M W _ _ _
        (moduleCoefficientModule R M W) (moduleRepresentation R M W)
        (@Representation.IntertwiningMap.equivLinearMapAsModule R M V W _ _ _ _
          (moduleCoefficientModule R M V) (moduleCoefficientModule R M W)
          (moduleRepresentation R M V) (moduleRepresentation R M W) F x) =
      (moduleRepresentationMapEquiv R M).symm F
        (@Representation.asModuleEquiv R M V _ _ _
          (moduleCoefficientModule R M V) (moduleRepresentation R M V) x) := by
  rw [moduleRepresentationMapEquiv_symm_apply]
  rfl

end CommSemiring

end MonoidAlgebra

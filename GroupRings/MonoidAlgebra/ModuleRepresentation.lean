/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCrossedMaps
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The representation on a given monoid-algebra module

`MonoidAlgebra.moduleRepresentation` packages the canonical monoid action on the
original module, with exactly `MonoidAlgebra.moduleCoefficientModule` as its
coefficient module. It allows noncommutative and zero semirings. Original
monoid-algebra linear maps give intertwiners without changing their values.

The construction uses Mathlib's `Representation.ofDistribMulAction`. The
pointwise comparison with `Representation.ofModule` uses its scalar-restriction
equivalence rather than identifying coefficient-module dictionaries.
-/

@[expose] public section

noncomputable section

universe uR uM uV uW uU

namespace MonoidAlgebra

variable (R : Type uR) (M : Type uM) [Semiring R] [Monoid M]
variable (V : Type uV) [AddCommMonoid V] [Module (MonoidAlgebra R M) V]

/-- The canonical representation on a given monoid-algebra module, with its
coefficient action restricted along `singleOneRingHom`. -/
def moduleRepresentation :
    @Representation R M V _ _ _ (moduleCoefficientModule R M V) := by
  letI : Module R V := moduleCoefficientModule R M V
  letI : DistribMulAction M V := moduleMonoidAction R M V
  letI : SMulCommClass M R V := ⟨fun m r v => by
    change (single m 1 : MonoidAlgebra R M) • ((single 1 r : MonoidAlgebra R M) • v) =
      (single 1 r : MonoidAlgebra R M) • ((single m 1 : MonoidAlgebra R M) • v)
    rw [← mul_smul, ← mul_smul]
    simp⟩
  exact Representation.ofDistribMulAction R M V

/-- A monoid operator is the action of the corresponding scalar-one symbol. -/
@[simp]
theorem moduleRepresentation_apply (m : M) (v : V) :
    moduleRepresentation R M V m v = (single m (1 : R) : MonoidAlgebra R M) • v := rfl

/-- The representation packages the existing canonical monoid action. -/
theorem moduleRepresentation_apply_eq_moduleMonoidAction (m : M) (v : V) :
    moduleRepresentation R M V m v = (moduleMonoidAction R M V).smul m v := rfl

variable {V}
variable {W : Type uW} [AddCommMonoid W] [Module (MonoidAlgebra R M) W]
variable {U : Type uU} [AddCommMonoid U] [Module (MonoidAlgebra R M) U]

/-- An original monoid-algebra linear map, regarded as a coefficient-linear
intertwiner between the canonical representations. -/
def moduleRepresentationMap (f : V →ₗ[MonoidAlgebra R M] W) :
    letI : Module R V := moduleCoefficientModule R M V
    letI : Module R W := moduleCoefficientModule R M W
    Representation.IntertwiningMap (moduleRepresentation R M V) (moduleRepresentation R M W) := by
  letI : Module R V := moduleCoefficientModule R M V
  letI : Module R W := moduleCoefficientModule R M W
  exact
    { toLinearMap :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun r v => f.map_smul (single 1 r) v }
      isIntertwining' := fun m => LinearMap.ext fun v => f.map_smul (single m 1) v }

/-- Packaging a linear map does not change its evaluation. -/
@[simp]
theorem moduleRepresentationMap_apply (f : V →ₗ[MonoidAlgebra R M] W) (v : V) :
    moduleRepresentationMap R M f v = f v := rfl

/-- Evaluation on the original module makes the packaging faithful. -/
theorem moduleRepresentationMap_injective :
    Function.Injective (moduleRepresentationMap R M (V := V) (W := W)) := by
  intro f g h
  exact LinearMap.ext fun v => congrArg (fun k => k v) h

/-- Packaging preserves the identity map. -/
@[simp]
theorem moduleRepresentationMap_id :
    letI : Module R V := moduleCoefficientModule R M V
    moduleRepresentationMap R M (LinearMap.id : V →ₗ[MonoidAlgebra R M] V) =
      Representation.IntertwiningMap.id (moduleRepresentation R M V) := by
  let : Module R V := moduleCoefficientModule R M V
  ext v
  rfl

/-- Packaging preserves composition. -/
@[simp]
theorem moduleRepresentationMap_comp (g : W →ₗ[MonoidAlgebra R M] U)
    (f : V →ₗ[MonoidAlgebra R M] W) :
    letI : Module R V := moduleCoefficientModule R M V
    letI : Module R W := moduleCoefficientModule R M W
    letI : Module R U := moduleCoefficientModule R M U
    moduleRepresentationMap R M (g.comp f) =
      (moduleRepresentationMap R M g).comp (moduleRepresentationMap R M f) := by
  let : Module R V := moduleCoefficientModule R M V
  let : Module R W := moduleCoefficientModule R M W
  let : Module R U := moduleCoefficientModule R M U
  ext v
  rfl

end MonoidAlgebra

namespace MonoidAlgebra

variable (R : Type uR) (M : Type uM) [CommSemiring R] [Monoid M]
variable (V : Type uV) [AddCommMonoid V] [Module (MonoidAlgebra R M) V]

/-- Agreement with Mathlib's representation on the scalar-restriction synonym,
transported pointwise by its additive equivalence. -/
@[simp]
theorem moduleRepresentation_ofModule_apply (m : M) (v : RestrictScalars R R[M] V) :
    RestrictScalars.addEquiv R R[M] V (Representation.ofModule (k := R) (G := M) V m v) =
      moduleRepresentation R M V m (RestrictScalars.addEquiv R R[M] V v) := by
  simp [Representation.ofModule, MonoidAlgebra.lift_symm_apply,
    RestrictScalars.lsmul_apply_apply]

/-- Agreement with Mathlib's representation when a coefficient action and its
scalar tower have already been supplied. No equality of module dictionaries is needed. -/
theorem moduleRepresentation_ofModule'_apply [Module R V] [IsScalarTower R R[M] V]
    (m : M) (v : V) :
    moduleRepresentation R M V m v = Representation.ofModule' (k := R) (G := M) V m v := rfl

end MonoidAlgebra

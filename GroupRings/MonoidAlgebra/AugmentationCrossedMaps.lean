/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.AugmentationCotangent.Universal
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.Module.RingHom

/-! # Crossed maps for the full augmentation ideal

The cocycle predicate is Mathlib’s `groupCohomology.IsCocycle₁`.
The coefficient and monoid actions are induced by the given left module.
-/

@[expose] public section

noncomputable section

universe uR uM uV uW
namespace MonoidAlgebra
section ModuleAction
variable (R : Type uR) (M : Type uM) [Semiring R] [Monoid M]
variable (V : Type uV) [AddCommMonoid V] [Module (MonoidAlgebra R M) V]

/-- Restriction of the given module action along `m ↦ single m 1`. -/
@[instance_reducible]
def moduleMonoidAction : DistribMulAction M V where
  smul m v := (single m (1 : R) : MonoidAlgebra R M) • v
  one_smul v := by
    change (single 1 1 : MonoidAlgebra R M) • v = v
    simpa only [one_def] using (one_smul (MonoidAlgebra R M) v)
  mul_smul m n v := by
    change (single (m * n) 1 : MonoidAlgebra R M) • v =
      (single m 1 : MonoidAlgebra R M) • ((single n 1 : MonoidAlgebra R M) • v)
    simpa using (mul_smul (single m 1 : MonoidAlgebra R M)
      (single n 1 : MonoidAlgebra R M) v)
  smul_zero m := by change (single m (1 : R) : MonoidAlgebra R M) • (0 : V) = 0; simp
  smul_add m v w := by
    change (single m (1 : R) : MonoidAlgebra R M) • (v + w) = _
    exact smul_add _ _ _

/-- Coefficient scalars act through the canonical coefficient ring homomorphism. -/
@[instance_reducible]
def moduleCoefficientModule : Module R V :=
  Module.compHom V ((singleOneRingHom : R →+* MonoidAlgebra R M))

/-- The action formula holds for every label and every vector. -/
theorem moduleMonoidAction_apply (m : M) (v : V) :
    (moduleMonoidAction R M V).smul m v = (single m (1 : R) : MonoidAlgebra R M) • v := rfl

/-- Coefficients act on the left, including for noncommutative coefficient rings. -/
theorem moduleMonoidAction_coefficient (r : R) (m : M) (v : V) :
    (single m r : MonoidAlgebra R M) • v =
      (moduleCoefficientModule R M V).smul r ((moduleMonoidAction R M V).smul m v) := by
  change (single m r : MonoidAlgebra R M) • v =
    (single 1 r : MonoidAlgebra R M) • ((single m 1 : MonoidAlgebra R M) • v)
  rw [← mul_smul]
  simp

end ModuleAction
variable (R : Type uR) (M : Type uM) [Ring R] [Monoid M]
variable (V : Type uV) [AddCommGroup V] [Module R[M] V]

/-- Additive crossed maps for the canonical action on the given module.
This reuses Mathlib’s generic cocycle predicate, without a representation or topology. -/
def augmentationCocycles : AddSubgroup (M → V) :=
  letI : DistribMulAction M V := moduleMonoidAction R M V
  { carrier := {z | groupCohomology.IsCocycle₁ z}
    zero_mem' := by intro m n; simp
    add_mem' := by
      intro f g hf hg m n
      change f (m * n) + g (m * n) = m • (f n + g n) + (f m + g m)
      rw [hf m n, hg m n, smul_add]
      abel
    neg_mem' := by
      intro f hf m n
      change -f (m * n) = m • (-f n) + (-f m)
      rw [hf m n, smul_neg, neg_add] }

instance : CoeFun (augmentationCocycles R M V) (fun _ => M → V) :=
  ⟨fun z => z.1⟩

/-- Membership is precisely the normalized additive crossed-map law. -/
theorem mem_augmentationCocycles_iff (z : M → V) :
    z ∈ augmentationCocycles R M V ↔
      z 1 = 0 ∧ ∀ m n, z (m * n) = z m + (single m (1 : R) : MonoidAlgebra R M) • z n := by
  let : DistribMulAction M V := moduleMonoidAction R M V
  constructor
  · intro hz
    exact ⟨groupCohomology.map_one_of_isCocycle₁ hz,
      fun m n => (hz m n).trans (add_comm _ _)⟩
  · intro hz m n
    exact (hz.2 m n).trans (add_comm _ _)

/-- Evaluation satisfies the crossed multiplication law. -/
theorem augmentationCocycles_map_mul (z : augmentationCocycles R M V) (m n : M) :
    z (m * n) = z m + (single m (1 : R) : MonoidAlgebra R M) • z n :=
  ((mem_augmentationCocycles_iff R M V (z : M → V)).1 z.2).2 m n

/-- Evaluation separates crossed maps. -/
theorem augmentationCocycles_ext (z t : augmentationCocycles R M V)
    (h : ∀ m, z m = t m) : z = t := by
  apply Subtype.ext
  exact funext h

/-- The standard difference, as an element of the existing full kernel ideal. -/
def augmentationIdealDelta (m : M) : RingHom.ker (augmentation R M) :=
  ⟨single m 1 - 1, by
    change augmentation R M (single m 1 - 1) = 0
    simp⟩

/-- The underlying element is `[m] - 1`. -/
theorem augmentationIdealDelta_coe (m : M) :
    (augmentationIdealDelta R M m : MonoidAlgebra R M) = single m 1 - 1 := rfl

/-- The existing ideal carries the subtype of the left regular module action. -/
theorem augmentationIdeal_smul_coe (a : MonoidAlgebra R M)
    (x : RingHom.ker (augmentation R M)) :
    ((a • x : RingHom.ker (augmentation R M)) : MonoidAlgebra R M) =
      a * (x : MonoidAlgebra R M) := rfl

/-- The canonical action of the full ideal on a vector. -/
def augmentationIdealAction (v : V) :
    RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] V where
  toFun x := (x : MonoidAlgebra R M) • v
  map_add' x y := add_smul (x : MonoidAlgebra R M) (y : MonoidAlgebra R M) v
  map_smul' a x := mul_smul a (x : MonoidAlgebra R M) v

/-- Evaluation of the ideal action at every ideal element. -/
theorem augmentationIdealAction_apply (v : V) (x : RingHom.ker (augmentation R M)) :
    augmentationIdealAction R M V v x = (x : MonoidAlgebra R M) • v := rfl

/-- The coefficient sum uses the canonical coefficient action on the left. -/
def augmentationCrossedSum (z : augmentationCocycles R M V)
    (x : RingHom.ker (augmentation R M)) : V :=
  (coeffAddEquiv (x : MonoidAlgebra R M)).sum
    (fun m r => (single 1 r : MonoidAlgebra R M) • z m)

/-- Linear maps from the cotangent module to the given module, with coefficient
scalars restricted along `singleOneRingHom`. No ambient `Module R V` is needed. -/
abbrev AugmentationCotangentCoefficientHom :=
  letI : Module R V := moduleCoefficientModule R M V
  AugmentationCotangent R M →ₗ[R] V

/-- The existing cotangent correspondence with the canonical coefficient action. -/
abbrev augmentationCotangentCoefficientMap
    (L : AugmentationCotangentCoefficientHom R M V) : M →* Multiplicative V :=
  letI : Module R V := moduleCoefficientModule R M V
  augmentationCotangentEquiv R M L

/-- Cotangent evaluation is unchanged by naming the restricted coefficient action. -/
theorem augmentationCotangentCoefficientMap_apply
    (L : AugmentationCotangentCoefficientHom R M V) (m : M) :
    Multiplicative.toAdd (augmentationCotangentCoefficientMap R M V L m) =
      L (toAugmentationCotangent R M (augmentationIdealDelta R M m)) := by
  let : Module R V := moduleCoefficientModule R M V
  exact augmentationCotangentEquiv_apply R M L m

/-- Evaluation separates cotangent maps with the restricted coefficient action. -/
@[ext]
theorem augmentationCotangentCoefficientHom_ext
    (L K : AugmentationCotangentCoefficientHom R M V)
    (h : ∀ x, L x = K x) : L = K := by
  let : Module R V := moduleCoefficientModule R M V
  exact LinearMap.ext h

/-- Coefficient linearity uses the action inherited from the given monoid-algebra module. -/
theorem augmentationCotangentCoefficientHom_map_smul
    (L : AugmentationCotangentCoefficientHom R M V) (r : R)
    (x : AugmentationCotangent R M) :
    L (r • x) = (moduleCoefficientModule R M V).smul r (L x) := by
  let : Module R V := moduleCoefficientModule R M V
  exact L.map_smul r x

/-- Characteristic laws for an additive equivalence on the full ideal.
The final clause is the trivial-action cotangent comparison. -/
def IsAugmentationCrossedEquiv
    (e : (RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] V) ≃+
      augmentationCocycles R M V) : Prop :=
  (∀ F m, e F m = F (augmentationIdealDelta R M m)) ∧
  (∀ z x, e.symm z x = augmentationCrossedSum R M V z x) ∧
  (∀ v m, e (augmentationIdealAction R M V v) m =
    (single m (1 : R) : MonoidAlgebra R M) • v - v) ∧
  ((∀ m (v : V), (single m (1 : R) : MonoidAlgebra R M) • v = v) →
    ∀ (L : AugmentationCotangentCoefficientHom R M V),
      ∃ F : RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] V,
        (∀ x, F x = L (toAugmentationCotangent R M x)) ∧
        ∀ m, e F m = Multiplicative.toAdd (augmentationCotangentCoefficientMap R M V L m))

variable (W : Type uW) [AddCommGroup W] [Module (MonoidAlgebra R M) W]

/-- The full augmentation-ideal universal property, with coefficient-module
naturality. -/
def AugmentationCrossedUniversalProperty : Prop :=
  ∃ e : (RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] V) ≃+
      augmentationCocycles R M V,
    ∃ d : (RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] W) ≃+
        augmentationCocycles R M W,
      IsAugmentationCrossedEquiv R M V e ∧ IsAugmentationCrossedEquiv R M W d ∧
      ∀ (k : V →ₗ[MonoidAlgebra R M] W)
        (F : RingHom.ker (augmentation R M) →ₗ[MonoidAlgebra R M] V) m,
        d (k.comp F) m = k (e F m)

end MonoidAlgebra

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.MonoidAlgebra.FixedVectors
public import GroupRings.MonoidAlgebra.AugmentationCrossedMaps
public import GroupRings.RingTheory.Ideal.ModuleDetection

/-!
# Fixed vectors and coinvariants detect module maps

For a finite `p`-group over any ring in which the prime `p` vanishes, a linear
map of group-algebra modules is injective exactly when its map on fixed vectors
is injective, and surjective exactly when its map on coinvariants is surjective.
The modules may have unrelated universes and need not be finitely generated.

The fixed submodule is the common annihilator of the augmentation kernel,
restricted along the coefficient homomorphism. Coinvariants are the quotient
by the augmentation ideal times the whole module. All coefficient actions come
from the given group-algebra action via `moduleCoefficientModule`.

## References

For modular group rings, see D. S. Passman, *The Algebraic Structure of Group
Rings*, Wiley, 1977. The detection arguments here use uniform nilpotence of the
augmentation ideal and the corresponding general ideal-module results.
-/

@[expose] public section

noncomputable section

universe uR uM uV uW uX

namespace MonoidAlgebra

variable {R : Type uR} [Ring R] {M : Type uM} [Monoid M]
variable (V : Type uV) [AddCommGroup V] [Module (MonoidAlgebra R M) V]

/-- The fixed vectors of the given monoid-algebra module, as a coefficient-ring
submodule with its canonical restricted action. -/
def fixedVectors :
    letI := moduleCoefficientModule R M V
    Submodule R V := by
  letI := moduleCoefficientModule R M V
  letI : SMul R (MonoidAlgebra R M) :=
    SMul.comp (MonoidAlgebra R M) (singleOneRingHom : R →+* MonoidAlgebra R M)
  letI : IsScalarTower R (MonoidAlgebra R M) V := by
    constructor
    intro r a x
    exact mul_smul ((singleOneRingHom : R →+* MonoidAlgebra R M) r) a x
  exact (Ideal.annihilatorSubmodule V (RingHom.ker (augmentation R M))).restrictScalars R

variable {V}
variable {W : Type uW} [AddCommGroup W] [Module (MonoidAlgebra R M) W]
variable {X : Type uX} [AddCommGroup X] [Module (MonoidAlgebra R M) X]

/-- Membership in the fixed submodule means that every canonical symbol fixes
the vector in the original action. -/
@[simp]
theorem mem_fixedVectors_iff (x : V) :
    x ∈ fixedVectors (R := R) (M := M) V ↔ ∀ m : M, single m (1 : R) • x = x :=
  mem_annihilatorSubmodule_ker_augmentation_iff x

/-- The map on fixed vectors induced by a map of the given modules. -/
def fixedVectorMap (f : V →ₗ[MonoidAlgebra R M] W) :
    fixedVectors (R := R) (M := M) V →ₗ[R] fixedVectors (R := R) (M := M) W := by
  letI := moduleCoefficientModule R M V
  letI := moduleCoefficientModule R M W
  letI : SMul R (MonoidAlgebra R M) :=
    SMul.comp (MonoidAlgebra R M) (singleOneRingHom : R →+* MonoidAlgebra R M)
  letI : IsScalarTower R (MonoidAlgebra R M) V := by
    constructor
    intro r a x
    exact mul_smul ((singleOneRingHom : R →+* MonoidAlgebra R M) r) a x
  letI : IsScalarTower R (MonoidAlgebra R M) W := by
    constructor
    intro r a x
    exact mul_smul ((singleOneRingHom : R →+* MonoidAlgebra R M) r) a x
  exact (Ideal.annihilatorSubmoduleMap (RingHom.ker (augmentation R M)) f).restrictScalars R

/-- The fixed-vector map acts by the original map on every vector. -/
@[simp]
theorem fixedVectorMap_apply (f : V →ₗ[MonoidAlgebra R M] W)
    (x : fixedVectors (R := R) (M := M) V) : (fixedVectorMap f x : W) = f x := rfl

/-- The fixed-vector map preserves identity. -/
@[simp]
theorem fixedVectorMap_id :
    fixedVectorMap (LinearMap.id : V →ₗ[MonoidAlgebra R M] V) = LinearMap.id := by
  ext x
  rfl

/-- The fixed-vector map preserves composition. -/
@[simp]
theorem fixedVectorMap_comp (f : V →ₗ[MonoidAlgebra R M] W)
    (g : W →ₗ[MonoidAlgebra R M] X) :
    fixedVectorMap (g.comp f) = (fixedVectorMap g).comp (fixedVectorMap f) := by
  ext x
  rfl

/-- The canonical map on the augmentation-ideal-action quotients, with the
coefficient action restricted from each quotient's given group-algebra action. -/
def coinvariantMap (f : V →ₗ[MonoidAlgebra R M] W) :
    letI := moduleCoefficientModule R M
      (V ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) V)))
    letI := moduleCoefficientModule R M
      (W ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) W)))
    (V ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) V))) →ₗ[R]
      W ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) W)) := by
  let I := RingHom.ker (augmentation R M)
  letI := moduleCoefficientModule R M (V ⧸ (I • (⊤ : Submodule (MonoidAlgebra R M) V)))
  letI := moduleCoefficientModule R M (W ⧸ (I • (⊤ : Submodule (MonoidAlgebra R M) W)))
  let q := (I • (⊤ : Submodule (MonoidAlgebra R M) V)).mapQ
    (I • (⊤ : Submodule (MonoidAlgebra R M) W)) f
    (Submodule.smul_top_le_comap_smul_top I f)
  letI : SMul R (MonoidAlgebra R M) :=
    SMul.comp (MonoidAlgebra R M) (singleOneRingHom : R →+* MonoidAlgebra R M)
  letI : IsScalarTower R (MonoidAlgebra R M)
      (V ⧸ (I • (⊤ : Submodule (MonoidAlgebra R M) V))) := by
    constructor
    intro r a x
    exact mul_smul ((singleOneRingHom : R →+* MonoidAlgebra R M) r) a x
  letI : IsScalarTower R (MonoidAlgebra R M)
      (W ⧸ (I • (⊤ : Submodule (MonoidAlgebra R M) W))) := by
    constructor
    intro r a x
    exact mul_smul ((singleOneRingHom : R →+* MonoidAlgebra R M) r) a x
  exact q.restrictScalars R

/-- On quotient classes the map is `[x] ↦ [f x]`. -/
@[simp]
theorem coinvariantMap_mk (f : V →ₗ[MonoidAlgebra R M] W) (x : V) :
    coinvariantMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

/-- The coinvariant map of the identity fixes every quotient element. -/
@[simp]
theorem coinvariantMap_id_apply
    (x : V ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) V))) :
    coinvariantMap (LinearMap.id : V →ₗ[MonoidAlgebra R M] V) x = x := by
  obtain ⟨x⟩ := x
  rfl

/-- The coinvariant map of a composition is the composition on every quotient element. -/
@[simp]
theorem coinvariantMap_comp_apply (f : V →ₗ[MonoidAlgebra R M] W)
    (g : W →ₗ[MonoidAlgebra R M] X)
    (x : V ⧸ (RingHom.ker (augmentation R M) • (⊤ : Submodule (MonoidAlgebra R M) V))) :
    coinvariantMap (g.comp f) x = coinvariantMap g (coinvariantMap f x) := by
  obtain ⟨x⟩ := x
  rfl

variable {G : Type uM} [Group G] [Finite G]
variable {U : Type uV} [AddCommGroup U] [Module (MonoidAlgebra R G) U]
variable {Z : Type uW} [AddCommGroup Z] [Module (MonoidAlgebra R G) Z]

/-- Over a finite `p`-group algebra in which the prime `p` vanishes, restriction
to canonical fixed vectors detects injectivity of every module map. -/
theorem injective_iff_fixedVectorMap {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0)
    (hG : IsPGroup p G) (f : U →ₗ[MonoidAlgebra R G] Z) :
    Function.Injective f ↔ Function.Injective (fixedVectorMap f) := by
  exact LinearMap.injective_iff_annihilatorSubmoduleMap
    (RingHom.ker (augmentation R G)) ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩ f

/-- Over a finite `p`-group algebra in which the prime `p` vanishes, the canonical
map on augmentation coinvariants detects surjectivity of every module map. -/
theorem surjective_iff_coinvariantMap {p : ℕ} (hp : p.Prime) (hR : (p : R) = 0)
    (hG : IsPGroup p G) (f : U →ₗ[MonoidAlgebra R G] Z) :
    Function.Surjective f ↔ Function.Surjective (coinvariantMap f) := by
  exact LinearMap.surjective_iff_mapQ_smul_top
    (RingHom.ker (augmentation R G)) ⟨Nat.card G, augmentation_pow_card_eq_bot hp hR hG⟩ f

end MonoidAlgebra

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import GroupRings.MonoidAlgebra.AugmentationCrossedMaps
public import Mathlib.Tactic.NoncommRing
/-! # Universal property of the augmentation ideal

Linear maps from the full augmentation ideal correspond to normalized additive
crossed maps. Coefficients act on the left; the coefficient ring need not commute.
-/
@[expose] public section
noncomputable section
universe uR uM uV uW
namespace MonoidAlgebra
variable (R : Type uR) (M : Type uM) [Ring R] [Monoid M]
variable (V : Type uV) [AddCommGroup V] [Module R[M] V]

/-- Coefficientwise additive extension of a crossed map. -/
def augmentationCocycleExtension (z : augmentationCocycles R M V) : R[M] →+ V where
  toFun a := a.coeff.sum fun m r => (single 1 r : R[M]) • z m
  map_zero' := by simp
  map_add' a b := by
    classical
    simp only [coeff_add]
    exact Finsupp.sum_add_index (by simp) (by simp [add_smul])

private theorem augmentationCocycleExtension_single (z : augmentationCocycles R M V)
    (m : M) (r : R) :
    augmentationCocycleExtension R M V z (single m r) = (single 1 r : R[M]) • z m := by
  change (single m r : R[M]).coeff.sum (fun n s => (single 1 s : R[M]) • z n) = _
  simp

private theorem cocycle_one (z : augmentationCocycles R M V) : z 1 = 0 :=
  ((mem_augmentationCocycles_iff R M V z).mp z.property).1

private theorem augmentationCocycleExtension_single_mul (z : augmentationCocycles R M V)
    (n : M) (s : R) (a : R[M]) :
    augmentationCocycleExtension R M V z (single n s * a) =
      (single 1 (s * augmentation R M a) : R[M]) • z n +
        (single n s : R[M]) • augmentationCocycleExtension R M V z a := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [mul_add, map_add, ha, hb, mul_add, single_add, add_smul, smul_add]
      abel
  | single m r =>
      simp only [single_mul_single, augmentationCocycleExtension_single, augmentation_single]
      rw [augmentationCocycles_map_mul]
      simp only [smul_add, smul_smul, single_mul_single, one_mul, mul_one]

private theorem augmentationCocycleExtension_smul (z : augmentationCocycles R M V)
    (a : R[M]) (x : RingHom.ker (augmentation R M)) :
    augmentationCocycleExtension R M V z (a * x.val) =
      a • augmentationCocycleExtension R M V z x.val := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, ha, hb, add_smul]
  | single m r =>
      rw [augmentationCocycleExtension_single_mul]
      have hx : augmentation R M x.val = 0 := x.property
      simp [hx]

/-- The linear extension of an augmentation cocycle to the full augmentation ideal. -/
def augmentationCocycleLift (z : augmentationCocycles R M V) :
    RingHom.ker (augmentation R M) →ₗ[R[M]] V where
  toFun x := augmentationCocycleExtension R M V z x.val
  map_add' x y := (augmentationCocycleExtension R M V z).map_add x.val y.val
  map_smul' a x := by
    change augmentationCocycleExtension R M V z (a * x.val) = _
    exact augmentationCocycleExtension_smul R M V z a x

theorem augmentationCocycleLift_apply (z : augmentationCocycles R M V)
    (x : RingHom.ker (augmentation R M)) :
    augmentationCocycleLift R M V z x = augmentationCrossedSum R M V z x := rfl

@[simp] theorem augmentationIdealDelta_one : augmentationIdealDelta R M 1 = 0 := by
  apply Subtype.ext
  simp [augmentationIdealDelta_coe, ← one_def]

theorem augmentationIdealDelta_mul (m n : M) :
    augmentationIdealDelta R M (m * n) =
      augmentationIdealDelta R M m + (single m 1 : R[M]) • augmentationIdealDelta R M n := by
  apply Subtype.ext
  change (single (m * n) (1 : R) : R[M]) - 1 =
    (single m 1 - 1) + single m 1 * (single n 1 - 1)
  rw [mul_sub, mul_one, single_mul_single, one_mul]
  abel

/-- Evaluation of a linear map on the canonical augmentation differences. -/
def augmentationLinearToCocycle
    (F : RingHom.ker (augmentation R M) →ₗ[R[M]] V) : augmentationCocycles R M V :=
  ⟨fun m => F (augmentationIdealDelta R M m),
    (mem_augmentationCocycles_iff R M V _).mpr ⟨by simp, by
      intro m n
      rw [augmentationIdealDelta_mul, map_add, map_smul]⟩⟩

@[simp] theorem augmentationLinearToCocycle_apply
    (F : RingHom.ker (augmentation R M) →ₗ[R[M]] V) (m : M) :
    augmentationLinearToCocycle R M V F m = F (augmentationIdealDelta R M m) := rfl

/-- The additive projection onto the augmentation kernel. -/
def augmentationProjection : R[M] →+ RingHom.ker (augmentation R M) where
  toFun a := ⟨a - single 1 (augmentation R M a), by simp⟩
  map_zero' := by ext; simp
  map_add' a b := by
    apply Subtype.ext
    change a + b - single 1 (augmentation R M (a + b)) =
      (a - single 1 (augmentation R M a)) + (b - single 1 (augmentation R M b))
    rw [map_add, single_add]
    abel

@[simp] theorem augmentationProjection_coe (a : R[M]) :
    ((augmentationProjection R M) a : R[M]) = a - single 1 (augmentation R M a) := rfl

theorem augmentationProjection_single (m : M) (r : R) :
    augmentationProjection R M (single m r) =
      (single 1 r : R[M]) • augmentationIdealDelta R M m := by
  apply Subtype.ext
  simp [augmentationProjection_coe,
    augmentationIdealDelta_coe, mul_sub, single_mul_single]

@[simp] theorem augmentationProjection_mem (x : RingHom.ker (augmentation R M)) :
    augmentationProjection R M x.val = x := by
  apply Subtype.ext
  have hx : augmentation R M x.val = 0 := x.property
  simp [augmentationProjection_coe, hx]

@[simp] theorem augmentationCocycleLift_delta (z : augmentationCocycles R M V) (m : M) :
    augmentationCocycleLift R M V z (augmentationIdealDelta R M m) = z m := by
  change augmentationCocycleExtension R M V z (single m 1 - 1) = _
  rw [map_sub, one_def, augmentationCocycleExtension_single, augmentationCocycleExtension_single]
  simp [cocycle_one, ← one_def]

@[simp] theorem augmentationCocycleLift_toCocycle
    (F : RingHom.ker (augmentation R M) →ₗ[R[M]] V) :
    augmentationCocycleLift R M V (augmentationLinearToCocycle R M V F) = F := by
  have h (a : R[M]) : augmentationCocycleExtension R M V (augmentationLinearToCocycle R M V F) a =
      F (augmentationProjection R M a) := by
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single m r =>
        rw [augmentationCocycleExtension_single, augmentationProjection_single, map_smul]
        rfl
  ext x
  change augmentationCocycleExtension R M V (augmentationLinearToCocycle R M V F) x.val = _
  simpa using h x.val


/-- Linear maps from the full augmentation ideal represent normalized crossed maps. -/
def augmentationCrossedEquiv :
    (RingHom.ker (augmentation R M) →ₗ[R[M]] V) ≃+ augmentationCocycles R M V where
  toFun := augmentationLinearToCocycle R M V
  invFun := augmentationCocycleLift R M V
  left_inv := augmentationCocycleLift_toCocycle R M V
  right_inv z := by
    apply Subtype.ext
    funext m
    exact augmentationCocycleLift_delta R M V z m
  map_add' F G := by
    apply Subtype.ext
    funext m
    rfl

@[simp] theorem augmentationCrossedEquiv_apply
    (F : RingHom.ker (augmentation R M) →ₗ[R[M]] V) (m : M) :
    augmentationCrossedEquiv R M V F m = F (augmentationIdealDelta R M m) := rfl

@[simp] theorem augmentationCrossedEquiv_symm_apply
    (z : augmentationCocycles R M V) (x : RingHom.ker (augmentation R M)) :
    (augmentationCrossedEquiv R M V).symm z x = augmentationCrossedSum R M V z x := rfl

theorem augmentationCrossedEquiv_natural
    (W : Type uW) [AddCommGroup W] [Module R[M] W]
    (k : V →ₗ[R[M]] W) (F : RingHom.ker (augmentation R M) →ₗ[R[M]] V) (m : M) :
    augmentationCrossedEquiv R M W (k.comp F) m = k (augmentationCrossedEquiv R M V F m) := rfl

theorem augmentationCrossedEquiv_principal (v : V) (m : M) :
    augmentationCrossedEquiv R M V (augmentationIdealAction R M V v) m =
      (single m 1 : R[M]) • v - v := by
  simp [augmentationCrossedEquiv_apply, augmentationIdealAction_apply,
    augmentationIdealDelta_coe, sub_smul]


/-- For trivial label action, the extension agrees on every ideal element with the cotangent map. -/
theorem augmentationCrossedEquiv_cotangent
    (h : ∀ (m : M) (v : V), (single m 1 : R[M]) • v = v) :
    ∀ L : AugmentationCotangentCoefficientHom R M V, ∃ F,
      (∀ x, F x = L (toAugmentationCotangent R M x)) ∧
      ∀ m, augmentationCrossedEquiv R M V F m =
        Multiplicative.toAdd (augmentationCotangentCoefficientMap R M V L m) := by
  let : Module R V := moduleCoefficientModule R M V
  intro L
  let c := augmentationCotangentEquiv R M L
  let z : augmentationCocycles R M V := ⟨fun m => Multiplicative.toAdd (c m),
    (mem_augmentationCocycles_iff R M V _).mpr ⟨by rw [map_one]; rfl, by
      intro m n
      rw [map_mul, h]
      rfl⟩⟩
  have hz (m : M) : z m = L (toAugmentationCotangent R M (augmentationIdealDelta R M m)) := by
    exact augmentationCotangentEquiv_apply R M L m
  have hc (r : R) (v : V) : r • v = (single 1 r : R[M]) • v := by
    rfl
  have he (a : R[M]) : augmentationCocycleExtension R M V z a =
      L (toAugmentationCotangent R M (augmentationProjection R M a)) := by
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single m r =>
        rw [augmentationCocycleExtension_single, augmentationProjection_single]
        have qt := toAugmentationCotangent_smul R M r (augmentationIdealDelta R M m)
        have qs : toAugmentationCotangent R M ((single 1 r : R[M]) • augmentationIdealDelta R M m) =
            r • toAugmentationCotangent R M (augmentationIdealDelta R M m) := by
          exact qt.symm
        rw [qs, map_smul, hc, hz]
  refine ⟨augmentationCocycleLift R M V z, ?_, ?_⟩
  · intro x
    change augmentationCocycleExtension R M V z x.val = _
    simpa using he x.val
  · intro m
    exact augmentationCocycleLift_delta R M V z m

/-- The canonical equivalence satisfies the coefficient, principal and cotangent laws. -/
theorem augmentationCrossedEquiv_isAugmentationCrossedEquiv :
    IsAugmentationCrossedEquiv R M V (augmentationCrossedEquiv R M V) := by
  refine ⟨fun F m => rfl, fun z x => rfl, ?_, ?_⟩
  · exact augmentationCrossedEquiv_principal R M V
  · exact augmentationCrossedEquiv_cotangent R M V


/-- The augmentation universal property, natural in both target modules. -/
theorem augmentationCrossedUniversalProperty
    (W : Type uW) [AddCommGroup W] [Module R[M] W] :
    AugmentationCrossedUniversalProperty R M V W := by
  refine ⟨augmentationCrossedEquiv R M V, augmentationCrossedEquiv R M W, ?_, ?_, ?_⟩
  · exact augmentationCrossedEquiv_isAugmentationCrossedEquiv R M V
  · exact augmentationCrossedEquiv_isAugmentationCrossedEquiv R M W
  · intro k F m; rfl


theorem augmentationCrossedEquiv_symm_formula
    (z : augmentationCocycles R M V) (x : RingHom.ker (augmentation R M)) :
    (augmentationCrossedEquiv R M V).symm z x =
      x.val.coeff.sum (fun m r => (single 1 r : R[M]) • z m) := rfl

@[simp] theorem augmentationCocycles_one (z : augmentationCocycles R M V) : z 1 = 0 :=
  cocycle_one R M V z

/-- Maps from the full ideal are determined by their augmentation differences. -/
theorem augmentationIdeal_linearMap_ext
    {F G : RingHom.ker (augmentation R M) →ₗ[R[M]] V}
    (h : ∀ m, F (augmentationIdealDelta R M m) = G (augmentationIdealDelta R M m)) : F = G := by
  apply (augmentationCrossedEquiv R M V).injective
  apply Subtype.ext
  exact funext h


@[simp] theorem augmentationCocycles_zero_apply (m : M) :
    (0 : augmentationCocycles R M V) m = 0 := rfl

@[simp] theorem augmentationCocycles_add_apply (z w : augmentationCocycles R M V) (m : M) :
    (z + w) m = z m + w m := rfl

@[simp] theorem augmentationCocycles_neg_apply (z : augmentationCocycles R M V) (m : M) :
    (-z) m = -z m := rfl

@[simp] theorem augmentationCocycles_sub_apply (z w : augmentationCocycles R M V) (m : M) :
    (z - w) m = z m - w m := rfl

@[simp] theorem augmentationCocycleExtension_apply
    (z : augmentationCocycles R M V) (a : R[M]) :
    augmentationCocycleExtension R M V z a =
      a.coeff.sum (fun m r => (single 1 r : R[M]) • z m) := rfl

end MonoidAlgebra

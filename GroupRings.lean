/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.FreeAbelian.LaurentPolynomial
public import GroupRings.FiniteAbelian.RightConvolution
public import GroupRings.MonoidAlgebra.AugmentationBasis
public import GroupRings.MonoidAlgebra.AugmentationGenerators
public import GroupRings.MonoidAlgebra.CoefficientChange
public import GroupRings.MonoidAlgebra.Units
public import GroupRings.MonoidAlgebra.SubgroupIdeals
public import GroupRings.MonoidAlgebra.SubgroupIdealsFG
public import GroupRings.MonoidAlgebra.Quotient
public import GroupRings.MonoidAlgebra.Noetherian
public import GroupRings.MonoidAlgebra.MapDomain
public import GroupRings.RingTheory.Noetherian

/-!
# Monoid-algebra units, augmentation, Laurent coordinates and character convolution

The public entry point for the multivariable Laurent model, explicit-coordinate
algebra equivalence and canonical free-abelian specialization with basis laws,
as well as generic-field character bases, right convolution, diagonalization
and rank on finite abelian groups. Monoid-algebra augmentation is available over
any semiring, with its kernel generated as a left ideal by basis differences
over any ring. A monoid generating set, or a subgroup generating set for a
group, suffices for these left-ideal generators. The kernel also has a left
coefficient-ring module basis indexed by the nonidentity monoid elements.
Single-term units over a nontrivial semiring are characterized by unit
coefficients and unit monoid indices, without commutativity or
cancellation assumptions; coefficient-unit reflection needs no nontriviality.
Subgroup differences generate the left ideal of elements with zero coefficient
sums on left cosets, over any ring. Over a nontrivial ring these ideals detect
subgroup membership and order, and two-sidedness detects normality. The subgroup
left ideal is finitely generated whenever the subgroup is; over a nontrivial
ring the converse holds, including for the augmentation kernel and the whole group.
A left-Noetherian group algebra over a nontrivial ring has every subgroup finitely
generated. Surjective augmentation also allows left-Noetherianity to descend to
the coefficient semiring, using Mathlib's generic transport theorem.
Over every semiring, left-Noetherianity descends from a monoid algebra to the
algebra of any embedded group, hence to every subgroup algebra. Coefficient
projection supplies an additive right retraction, and a generic ideal
extension-contraction criterion transports the ascending chain condition.
-/

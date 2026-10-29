/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupRings.FreeAbelian.LaurentPolynomial
public import GroupRings.FiniteAbelian.RightConvolution
public import GroupRings.MonoidAlgebra.AugmentationBasis
public import GroupRings.MonoidAlgebra.AugmentationGenerators
public import GroupRings.MonoidAlgebra.Units
public import GroupRings.MonoidAlgebra.SubgroupIdeals

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
subgroup membership and order, and two-sidedness detects normality.
-/

# Simple modules of finite p-group algebras

Import `GroupRings` or `GroupRings.MonoidAlgebra.SimpleModules`.

Let `R` be any unital ring, `G` a finite `p`-group, and `p` a prime with
`(p : R) = 0`. For any unital left `MonoidAlgebra R G`-module `V`,
`MonoidAlgebra.isSimpleModule_iff_of_isPGroup` proves

```lean
IsSimpleModule (MonoidAlgebra R G) V ↔
  @IsSimpleModule R _ V _
    (Module.compHom V (MonoidAlgebra.singleOneRingHom (R := R) (M := G)))
```

This uses Mathlib's `IsSimpleModule`, not a separate notion of simple
representation. Coefficients can be noncommutative or zero. The ring, group
and module have independent universes; no finiteness, finite generation or
dimension assumption on `V` is used. The literal cast-equality hypothesis
is sufficient; no chosen `CharP R p` instance is required.

## Canonical action and characteristic API

The restricted coefficient action is exactly
`r • x = MonoidAlgebra.singleOneRingHom r • x`. It is Mathlib's
`Module.compHom` restriction, not an arbitrary compatible action supplied by
the caller. Its scalar formula is Mathlib's `MulAction.compHom_smul_def`,
together with `MonoidAlgebra.singleOneRingHom_apply`.

For a simple module, the theorem
`MonoidAlgebra.smul_eq_augmentation_smul_of_isSimpleModule_of_isPGroup`
gives, for **every** algebra element `a` and vector `x`,

```lean
a • x = MonoidAlgebra.singleOneRingHom
  (MonoidAlgebra.augmentation R G a) • x
```

Equivalently, `single_smul_eq_of_isSimpleModule_of_isPGroup` says that
`single g 1 • x = x` for every `g` and `x`. This is stronger than existence
of a single nonzero fixed vector. For example, the regular `F₂[C₂]` module
has the nonzero fixed vector `1 + g`, but `g` does not fix `1`, and the
module is not simple.

The characteristic equivalence `smul_eq_augmentation_smul_iff` has the
stronger scope of any semiring, monoid and semimodule. It identifies the
all-scalars augmentation formula with the all-symbols fixedness condition.
For rings, `isSimpleModule_iff_of_single_smul_eq` transports simplicity
under this condition using the **surjective augmentation**, not the usually
nonsurjective coefficient inclusion. The reverse implication from
coefficient simplicity, `isSimpleModule_of_isSimpleModule_singleOne`,
needs no condition on the monoid or its action.

## Proof and boundary cases

The existing augmentation-kernel common-annihilator submodule is nonzero
by uniform nilpotence of its action. In a simple module it must be the
whole module, so every group symbol fixes every vector. Mathlib's
bijective-semilinear-map simplicity theorem then applies to the identity
on vectors with scalar map given by augmentation.

No extra nontriviality hypothesis is needed: over the zero ring every
unital module is trivial and both simplicity predicates are false. The
characteristic hypothesis is essential to the action conclusion: the
characteristic-zero sign action of `C₂` on `ℚ` is simple but nontrivial.
The [public-import client](../tests/GroupRingsTest/SimpleModulesClient.lean)
uses the fixedness theorem to show the regular module is not simple when
the group is nontrivial, and checks a prime-field augmentation module.

For background see D. S. Passman, *The Algebraic Structure of Group Rings*,
Wiley, 1977. The implementation reuses the library's common-annihilator
and fixed-vector API and Mathlib's scalar-restriction and simplicity APIs.

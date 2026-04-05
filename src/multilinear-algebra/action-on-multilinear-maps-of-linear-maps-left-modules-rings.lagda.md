# Action on multilinear maps of linear maps between left modules over rings

```agda
module multilinear-algebra.action-on-multilinear-maps-of-linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.finite-sequences-in-left-modules-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
open import lists.insert-at-index-finite-sequences

open import multilinear-algebra.multilinear-maps-left-modules-rings

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Let `U`, `V` and `W` be three
[left modules](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) `R` and `n : ℕ` a
[natural number](elementary-number-theory.natural-numbers.md); let `f : Uⁿ → V`
be a
[multilinear map](multilinear-algebra.multilinear-maps-left-modules-rings.md).
Postcomposition with a
[linear map](linear-algebra.linear-maps-left-modules-rings.md) `g : V → W`
induces a multilinear map:

```text
  (x₁,...,xₙ) ↦ g (f (x₁,...,xₙ))
```

On the other hand, for any linear map `h : U → V` and multilinear map
`f : Vⁿ → W`, the map `Uⁿ → W` defined by

```text
  (x₁,...,xₙ) ↦ f (h x₁,...,h xₙ)
```

is multilinear.

This defines the
{{#concept "action on multilinear maps of linear maps" Disambiguation="between left modules over a ring" Agda=precomp-linear-map-multilinear-map-left-module-Ring}}
between left modules over a ring.

## Definitions

### Postcomposition of a multilinear map by a linear map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (W : left-module-Ring l4 R)
  (h : linear-map-left-module-Ring R V W)
  where

  map-comp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    (f : multilinear-map-left-module-Ring R U V n) →
    type-fin-sequence-left-module-Ring R U n →
    type-left-module-Ring R W
  map-comp-linear-map-multilinear-map-left-module-Ring n f =
    map-linear-map-left-module-Ring R V W h ∘
    map-multilinear-map-left-module-Ring R U V n f
```

### Precomposition of a multilinear map by a linear map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (W : left-module-Ring l4 R)
  (h : linear-map-left-module-Ring R U V)
  where

  map-precomp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    multilinear-map-left-module-Ring R V W n →
    type-fin-sequence-left-module-Ring R U n →
    type-left-module-Ring R W
  map-precomp-linear-map-multilinear-map-left-module-Ring n f =
    map-multilinear-map-left-module-Ring R V W n f ∘
    map-fin-sequence n (map-linear-map-left-module-Ring R U V h)
```

## Properties

### Postcomposition with a linear map produces a multilinear map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (W : left-module-Ring l4 R)
  (h : linear-map-left-module-Ring R V W)
  where

  is-multilinear-map-comp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    (f : multilinear-map-left-module-Ring R U V n) →
    is-multilinear-map-left-module-Ring R U W n
      ( map-comp-linear-map-multilinear-map-left-module-Ring R U V W h n f)
  is-multilinear-map-comp-linear-map-multilinear-map-left-module-Ring zero-ℕ f =
    is-linear-map-comp-left-module-Ring
      ( R)
      ( fin-sequence-left-module-Ring R U zero-ℕ)
      ( V)
      ( W)
      ( map-linear-map-left-module-Ring R V W h)
      ( map-multilinear-map-left-module-Ring R U V zero-ℕ f)
      ( is-linear-map-linear-map-left-module-Ring R V W h)
      ( is-multilinear-map-multilinear-map-left-module-Ring R U V zero-ℕ f)
  is-multilinear-map-comp-linear-map-multilinear-map-left-module-Ring
    (succ-ℕ n) f i u =
    is-linear-map-comp-left-module-Ring
      ( R)
      ( U)
      ( V)
      ( W)
      ( map-linear-map-left-module-Ring R V W h)
      ( eval-at-multilinear-map-left-module-Ring R U V n f i u)
      ( is-linear-map-linear-map-left-module-Ring R V W h)
      ( is-multilinear-map-multilinear-map-left-module-Ring R U V
        ( succ-ℕ n)
        ( f)
        ( i)
        ( u))

  comp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    multilinear-map-left-module-Ring R U V n →
    multilinear-map-left-module-Ring R U W n
  comp-linear-map-multilinear-map-left-module-Ring n f =
    ( map-comp-linear-map-multilinear-map-left-module-Ring R U V W h n f ,
      is-multilinear-map-comp-linear-map-multilinear-map-left-module-Ring n f)
```

### Precomposition with a linear map produces a multilinear map

```agda
module _
  {l1 l2 l3 l4 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (W : left-module-Ring l4 R)
  (h : linear-map-left-module-Ring R U V)
  where

  is-multilinear-map-precomp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    (f : multilinear-map-left-module-Ring R V W n) →
    is-multilinear-map-left-module-Ring R U W n
      ( map-precomp-linear-map-multilinear-map-left-module-Ring R U V W h n f)
  is-multilinear-map-precomp-linear-map-multilinear-map-left-module-Ring
    zero-ℕ f =
    is-linear-map-htpy-left-module-Ring
      ( R)
      ( fin-sequence-left-module-Ring R U zero-ℕ)
      ( W)
      ( λ u →
        inv
          ( is-zero-empty-multilinear-map-left-module-Ring R V W f
            ( map-fin-sequence
              ( zero-ℕ)
              ( map-linear-map-left-module-Ring R U V h)
              ( u))))
      ( is-linear-const-zero-map-left-module-Ring
        ( R)
        ( fin-sequence-left-module-Ring R U zero-ℕ)
        ( W))

  is-multilinear-map-precomp-linear-map-multilinear-map-left-module-Ring
    (succ-ℕ n) f i u =
    is-linear-map-htpy-left-module-Ring R U W
      ( λ x →
        ap
          ( map-multilinear-map-left-module-Ring R V W (succ-ℕ n) f)
          ( eq-htpy
            ( htpy-map-insert-at-fin-sequence
              ( map-linear-map-left-module-Ring R U V h)
              ( n)
              ( x)
              ( i)
              ( u))))
      ( is-linear-map-comp-left-module-Ring R U V W
        ( λ x →
          map-multilinear-map-left-module-Ring R V W (succ-ℕ n) f
            ( insert-at-fin-sequence n x i
              ( map-fin-sequence n
                ( map-linear-map-left-module-Ring R U V h)
                ( u))))
        ( map-linear-map-left-module-Ring R U V h)
        ( is-multilinear-map-multilinear-map-left-module-Ring R V W
          (succ-ℕ n)
          ( f)
          ( i)
          ( map-fin-sequence n (map-linear-map-left-module-Ring R U V h) u))
        ( is-linear-map-linear-map-left-module-Ring R U V h))

  precomp-linear-map-multilinear-map-left-module-Ring :
    (n : ℕ) →
    multilinear-map-left-module-Ring R V W n →
    multilinear-map-left-module-Ring R U W n
  precomp-linear-map-multilinear-map-left-module-Ring n f =
    ( map-precomp-linear-map-multilinear-map-left-module-Ring R U V W h n f ,
      is-multilinear-map-precomp-linear-map-multilinear-map-left-module-Ring
        ( n)
        ( f))
```

### The action on multilinear maps of linear maps is functorial

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (n : ℕ)
  where

  compute-precomp-id-linear-map-multilinear-map-left-module-Ring :
    ( precomp-linear-map-multilinear-map-left-module-Ring
      ( R)
      ( U)
      ( U)
      ( V)
      ( id-linear-map-left-module-Ring R U)
      ( n)) ~
    ( id)
  compute-precomp-id-linear-map-multilinear-map-left-module-Ring f =
    eq-htpy-multilinear-map-left-module-Ring
      ( R)
      ( U)
      ( V)
      ( n)
      ( refl-htpy)

module _
  {l1 l2 l3 l4 l5 : Level}
  (R : Ring l1)
  (U : left-module-Ring l2 R)
  (V : left-module-Ring l3 R)
  (W : left-module-Ring l4 R)
  (Z : left-module-Ring l5 R)
  (g : linear-map-left-module-Ring R V W)
  (h : linear-map-left-module-Ring R U V)
  (n : ℕ)
  where

  compute-precomp-comp-linear-map-multilinear-map-left-module-Ring :
    ( precomp-linear-map-multilinear-map-left-module-Ring R U W Z
      ( comp-linear-map-left-module-Ring R U V W g h)
      ( n)) ~
    ( precomp-linear-map-multilinear-map-left-module-Ring R U V Z h n ∘
      precomp-linear-map-multilinear-map-left-module-Ring R V W Z g n)
  compute-precomp-comp-linear-map-multilinear-map-left-module-Ring f =
    eq-htpy-multilinear-map-left-module-Ring
      ( R)
      ( U)
      ( Z)
      ( n)
      ( refl-htpy)
```

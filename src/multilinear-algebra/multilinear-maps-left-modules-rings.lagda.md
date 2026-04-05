# Multilinear maps between left modules over rings

```agda
module multilinear-algebra.multilinear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.addition-linear-maps-left-modules-rings
open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.finite-sequences-in-left-modules-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.subsets-left-modules-rings

open import lists.finite-sequences
open import lists.insert-at-index-finite-sequences

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Let `M` and `N` be two [left modules](linear-algebra.left-modules-rings.md) over
a [ring](ring-theory.rings.md) `R` and `n : ℕ` a
[natural number](elementary-number-theory.natural-numbers.md); a map from the
type of [finite sequences](lists.finite-sequences.md) of `M` into `N`,
`f : Mⁿ → N` is called
{{#concept "multilinear" Disambiguation="map between left modules over a ring" Agda=is-multilinear-map-left-module-Ring WD="multilinear map" WDID=Q1952404}}
if it is [linear](linear-algebra.linear-maps-left-modules-rings.md) w.r.t each
coordinate: for any [index](univalent-combinatorics.standard-finite-types.md)
`i : Fin n` and any element `(u₁,...,uᵢ₋₁,uᵢ₊₁,...,uₙ)`, the map

```text
  x ↦ f (u₁,...,uᵢ₋₁,x,uᵢ₊₁,...,uₙ)
```

is linear.

The constant zero map is multilinear and the pointwise sum of multilinear maps
is multilinear.

Note:

- for `n ＝ 1`, `M¹ ≃ M` and this is equivalent to linearity;
- for `n ＝ 0`, `M⁰` is the trivial module and linearity of `f : M⁰ → N` is
  equivalent to `f` being `zero` in the module `N`.

## Definitions

### Multilinear maps between modules over a ring

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  is-multilinear-map-prop-left-module-Ring :
    (n : ℕ) →
    (type-fin-sequence-left-module-Ring R M n → type-left-module-Ring R N) →
    Prop (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-prop-left-module-Ring zero-ℕ =
    is-linear-map-prop-left-module-Ring
      ( R)
      ( fin-sequence-left-module-Ring R M zero-ℕ)
      ( N)
  is-multilinear-map-prop-left-module-Ring (succ-ℕ n) f =
    Π-Prop
      ( Fin (succ-ℕ n))
      ( λ i →
        Π-Prop
          ( type-fin-sequence-left-module-Ring R M n)
          ( λ u →
            is-linear-map-prop-left-module-Ring
              ( R)
              ( M)
              ( N)
              ( λ x → f ( insert-at-fin-sequence n x i u))))

module _
  { l1 l2 l3 : Level}
  ( R : Ring l1)
  ( M : left-module-Ring l2 R)
  ( N : left-module-Ring l3 R)
  ( n : ℕ)
  ( f :
    type-fin-sequence-left-module-Ring R M n →
    type-left-module-Ring R N)
  where

  is-multilinear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-multilinear-map-left-module-Ring =
    type-Prop (is-multilinear-map-prop-left-module-Ring R M N n f)

  is-prop-is-multilinear-map-left-module-Ring :
    is-prop is-multilinear-map-left-module-Ring
  is-prop-is-multilinear-map-left-module-Ring =
    is-prop-type-Prop (is-multilinear-map-prop-left-module-Ring R M N n f)
```

### The type of multilinear maps between left modules

```agda
multilinear-map-left-module-Ring :
  {l1 l2 l3 : Level} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R) →
  (N : left-module-Ring l3 R) →
  (n : ℕ) →
  UU (l1 ⊔ l2 ⊔ l3)
multilinear-map-left-module-Ring R M N n =
  type-subtype
    ( is-multilinear-map-prop-left-module-Ring R M N n)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : multilinear-map-left-module-Ring R M N n)
  where

  map-multilinear-map-left-module-Ring :
    fin-sequence (type-left-module-Ring R M) n →
    type-left-module-Ring R N
  map-multilinear-map-left-module-Ring = pr1 f

  is-multilinear-map-multilinear-map-left-module-Ring :
    is-multilinear-map-left-module-Ring R M N n
      map-multilinear-map-left-module-Ring
  is-multilinear-map-multilinear-map-left-module-Ring = pr2 f
```

### Homotopies between multilinear maps

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f g : multilinear-map-left-module-Ring R M N n)
  where

  htpy-multilinear-map-left-module-Ring : UU (l2 ⊔ l3)
  htpy-multilinear-map-left-module-Ring =
    map-multilinear-map-left-module-Ring R M N n f ~
    map-multilinear-map-left-module-Ring R M N n g
```

## Properties

### Homotopic multilinear maps are equal

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  {f g : multilinear-map-left-module-Ring R M N n}
  where

  eq-htpy-multilinear-map-left-module-Ring :
    htpy-multilinear-map-left-module-Ring R M N n f g → f ＝ g
  eq-htpy-multilinear-map-left-module-Ring f~g =
    eq-type-subtype
      ( is-multilinear-map-prop-left-module-Ring R M N n)
      ( eq-htpy f~g)
```

### The constant zero map is multilinear

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  is-multilinear-const-zero-map-left-module-Ring :
    (n : ℕ) →
    is-multilinear-map-left-module-Ring R M N n
      (λ _ → zero-left-module-Ring R N)
  is-multilinear-const-zero-map-left-module-Ring zero-ℕ =
    is-linear-const-zero-map-left-module-Ring
      ( R)
      ( fin-sequence-left-module-Ring R M zero-ℕ)
      ( N)
  is-multilinear-const-zero-map-left-module-Ring (succ-ℕ n) i u =
    is-linear-const-zero-map-left-module-Ring
      ( R)
      ( M)
      ( N)

  zero-multilinear-map-left-module-Ring :
    (n : ℕ) → multilinear-map-left-module-Ring R M N n
  zero-multilinear-map-left-module-Ring n =
    ( ( λ _ → zero-left-module-Ring R N) ,
      ( is-multilinear-const-zero-map-left-module-Ring n))
```

### A multilinear map of rank zero is zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  is-zero-empty-multilinear-map-left-module-Ring :
    (f : multilinear-map-left-module-Ring R M N zero-ℕ) →
    (u : type-fin-sequence-left-module-Ring R M zero-ℕ) →
    is-zero-left-module-Ring R N
      ( map-multilinear-map-left-module-Ring R M N zero-ℕ f u)
  is-zero-empty-multilinear-map-left-module-Ring f u =
    inv-tr
      ( is-zero-left-module-Ring R N)
      ( ap
        ( map-multilinear-map-left-module-Ring R M N zero-ℕ f)
        ( is-zero-empty-fin-sequence-left-module-Ring R M u))
      ( is-zero-map-zero-linear-map-left-module-Ring
        ( R)
        ( fin-sequence-left-module-Ring R M zero-ℕ)
        ( N)
        ( f))

  is-zero-add-empty-multilinear-map-left-module-Ring :
    (f g : multilinear-map-left-module-Ring R M N zero-ℕ) →
    (u : type-fin-sequence-left-module-Ring R M zero-ℕ) →
    is-zero-left-module-Ring R N
      ( add-left-module-Ring R N
        ( map-multilinear-map-left-module-Ring R M N zero-ℕ f u)
        ( map-multilinear-map-left-module-Ring R M N zero-ℕ g u))
  is-zero-add-empty-multilinear-map-left-module-Ring f g u =
    ( ap-binary
      ( add-left-module-Ring R N)
      ( is-zero-empty-multilinear-map-left-module-Ring f u)
      ( is-zero-empty-multilinear-map-left-module-Ring g u)) ∙
    ( left-unit-law-add-left-module-Ring R N (zero-left-module-Ring R N))
```

### Multilinear maps of ranks `n + 1` induce `n + 1` linear maps

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (n : ℕ)
  (f : multilinear-map-left-module-Ring R M N (succ-ℕ n))
  where

  eval-at-multilinear-map-left-module-Ring :
    (i : Fin (succ-ℕ n)) →
    (u : type-fin-sequence-left-module-Ring R M n) →
    type-left-module-Ring R M →
    type-left-module-Ring R N
  eval-at-multilinear-map-left-module-Ring i u x =
    map-multilinear-map-left-module-Ring R M N (succ-ℕ n) f
      ( insert-at-fin-sequence n x i u)

  linear-map-at-multilinear-map-left-module-Ring :
    (i : Fin (succ-ℕ n)) →
    (u : type-fin-sequence-left-module-Ring R M n) →
    linear-map-left-module-Ring R M N
  linear-map-at-multilinear-map-left-module-Ring i u =
    ( eval-at-multilinear-map-left-module-Ring i u ,
      is-multilinear-map-multilinear-map-left-module-Ring
        ( R)
        ( M)
        ( N)
        ( succ-ℕ n)
        ( f)
        ( i)
        ( u))
```

### Linear maps are multilinear with rank `1`

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f : linear-map-left-module-Ring R M N)
  where

  map-multilinear-map-linear-map-left-module-Ring :
    type-fin-sequence-left-module-Ring R M 1 →
    type-left-module-Ring R N
  map-multilinear-map-linear-map-left-module-Ring u =
    map-linear-map-left-module-Ring R M N f
      (u (zero-Fin 0))

  is-multilinear-map-multilinear-map-linear-map-left-module-Ring :
    is-multilinear-map-left-module-Ring R M N 1
      map-multilinear-map-linear-map-left-module-Ring
  is-multilinear-map-multilinear-map-linear-map-left-module-Ring (inr x) u =
    is-linear-map-linear-map-left-module-Ring R M N f

  multilinear-map-linear-map-left-module-Ring :
    multilinear-map-left-module-Ring R M N 1
  multilinear-map-linear-map-left-module-Ring =
    ( map-multilinear-map-linear-map-left-module-Ring ,
      is-multilinear-map-multilinear-map-linear-map-left-module-Ring)
```

### The equivalence between linear maps and multilinear maps of rank `1`

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  linear-map-multilinear-map-left-module-Ring :
    multilinear-map-left-module-Ring R M N 1 →
    linear-map-left-module-Ring R M N
  linear-map-multilinear-map-left-module-Ring f =
    linear-map-at-multilinear-map-left-module-Ring R M N 0 f
      ( zero-Fin 0)
      ( empty-fin-sequence)

  is-section-multilinear-map-linear-map-left-module-Ring :
    multilinear-map-linear-map-left-module-Ring R M N ∘
    linear-map-multilinear-map-left-module-Ring ~
    id
  is-section-multilinear-map-linear-map-left-module-Ring f =
    eq-htpy-multilinear-map-left-module-Ring R M N 1
      ( λ u →
        ap
          ( map-multilinear-map-left-module-Ring R M N 1 f)
          ( eq-htpy (λ x → ap u (eq-is-contr (is-contr-Fin-1)))))

  is-retraction-multilinear-map-linear-map-left-module-Ring :
    linear-map-multilinear-map-left-module-Ring ∘
    multilinear-map-linear-map-left-module-Ring R M N ~
    id
  is-retraction-multilinear-map-linear-map-left-module-Ring f =
    refl

  is-equiv-multilinear-map-linear-map-left-module-Ring :
    is-equiv
      ( multilinear-map-linear-map-left-module-Ring R M N)
  is-equiv-multilinear-map-linear-map-left-module-Ring =
    is-equiv-is-invertible
      ( linear-map-multilinear-map-left-module-Ring)
      ( is-section-multilinear-map-linear-map-left-module-Ring)
      ( is-retraction-multilinear-map-linear-map-left-module-Ring)
```

### The sum of multilinear maps is multilinear

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  map-add-multilinear-map-left-module-Ring :
    (n : ℕ) →
    (f g : multilinear-map-left-module-Ring R M N n) →
    type-fin-sequence-left-module-Ring R M n →
    type-left-module-Ring R N
  map-add-multilinear-map-left-module-Ring n f g =
    add-left-module-Ring
      ( R)
      ( Π-left-module-Ring
        ( R)
        ( type-fin-sequence-left-module-Ring R M n)
        ( λ _ → N))
      ( map-multilinear-map-left-module-Ring R M N n f)
      ( map-multilinear-map-left-module-Ring R M N n g)

  is-multilinear-map-add-multilinear-map-left-module-Ring :
    (n : ℕ) →
    (f g : multilinear-map-left-module-Ring R M N n) →
    is-multilinear-map-left-module-Ring R M N n
      ( map-add-multilinear-map-left-module-Ring n f g)
  is-multilinear-map-add-multilinear-map-left-module-Ring zero-ℕ f g =
    is-linear-map-htpy-left-module-Ring
      ( R)
      ( fin-sequence-left-module-Ring R M zero-ℕ)
      ( N)
      ( inv ∘ is-zero-add-empty-multilinear-map-left-module-Ring R M N f g)
      ( is-linear-const-zero-map-left-module-Ring
        ( R)
        ( fin-sequence-left-module-Ring R M zero-ℕ)
        ( N))
  is-multilinear-map-add-multilinear-map-left-module-Ring (succ-ℕ n) f g i u =
    is-linear-map-add-linear-map-left-module-Ring R M N
      ( linear-map-at-multilinear-map-left-module-Ring R M N n f i u)
      ( linear-map-at-multilinear-map-left-module-Ring R M N n g i u)

  add-multilinear-map-left-module-Ring :
    (n : ℕ) →
    multilinear-map-left-module-Ring R M N n →
    multilinear-map-left-module-Ring R M N n →
    multilinear-map-left-module-Ring R M N n
  add-multilinear-map-left-module-Ring n f g =
    ( map-add-multilinear-map-left-module-Ring n f g ,
      is-multilinear-map-add-multilinear-map-left-module-Ring n f g)
```

### The subset of multilinear maps is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  is-closed-under-addition-subset-multinear-map-left-module-Ring :
    (n : ℕ) →
    is-closed-under-addition-subset-left-module-Ring
      ( R)
      ( Π-left-module-Ring
        ( R)
        ( type-fin-sequence-left-module-Ring R M n)
        ( λ _ → N))
      ( is-multilinear-map-prop-left-module-Ring R M N n)
  is-closed-under-addition-subset-multinear-map-left-module-Ring n f g H K =
    is-multilinear-map-add-multilinear-map-left-module-Ring R M N n
      ( f , H)
      ( g , K)
```

## External links

- [multilinear maps](https://ncatlab.org/nlab/show/multilinear+map) at $n$Lab
- [Multilinear maps](https://en.wikipedia.org/wiki/Multilinear_map) at Wikipedia

# The functor from the precategory of metric spaces and isometries to the precategory of metric spaces and short maps

```agda
module metric-spaces.functor-precategory-short-isometry-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import metric-spaces.isometry-metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-isometries
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

Because every [isometry](metric-spaces.isometry-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is also
[short](metric-spaces.short-functions-metric-spaces.md), there's a
[functor](category-theory.functor-precategories.md) between the
[precategory of metric spaces and isometries](metric-spaces.precategory-of-metric-spaces-and-isometries.md)
to the
[precategory of metric spaces and short maps](metric-spaces.precategory-of-metric-spaces-and-short-functions.md).

Moreover, since the map from isometry to short maps is an
[embedding](foundation.embeddings.md), this functor is
[faithful](category-theory.faithful-functors-precategories.md).

Finally, because short
[isomorphisms](category-theory.isomorphisms-in-precategories.md) are isometric,
this functor is also
[conservative](category-theory.conservative-functors-precategories.md).

## Definition

### The functor between the precatory of metric spaces and isometries to the precategory of metric spaces and short maps

```agda
module _
  (l1 l2 : Level)
  where

  functor-precategory-short-isometry-Metric-Space :
    functor-Precategory
      (precategory-isometry-Metric-Space {l1} {l2})
      (precategory-short-function-Metric-Space {l1} {l2})
  pr1 functor-precategory-short-isometry-Metric-Space A = A
  pr2 functor-precategory-short-isometry-Metric-Space =
    ( λ {A B} → short-isometry-Metric-Space A B) ,
    ( ( λ g f → refl) , ( λ A → refl))
```

## Properties

### The precategory functor from isometries to short maps is faithful

```agda
module _
  (l1 l2 : Level)
  where

  is-faithful-functor-precategory-short-isometry-Metric-Space :
    is-faithful-functor-Precategory
      (precategory-isometry-Metric-Space)
      (precategory-short-function-Metric-Space)
      (functor-precategory-short-isometry-Metric-Space l1 l2)
  is-faithful-functor-precategory-short-isometry-Metric-Space =
    is-emb-short-isometry-Metric-Space
```

### The precategory functor from isometries to short maps is conservative

```agda
module _
  (l1 l2 : Level)
  where

  is-conservative-functor-precategory-short-isometry-Metric-Space :
    is-conservative-functor-Precategory
      (precategory-isometry-Metric-Space)
      (precategory-short-function-Metric-Space)
      (functor-precategory-short-isometry-Metric-Space l1 l2)
  is-conservative-functor-precategory-short-isometry-Metric-Space {A} {B} f H =
    ( isometric-inv) ,
    ( eq-htpy-map-isometry-Metric-Space
      ( B)
      ( B)
      ( comp-isometry-Metric-Space B A B f isometric-inv)
      ( isometry-id-Metric-Space B)
      ( is-section-map-inv-is-equiv is-equiv-f)) ,
    ( eq-htpy-map-isometry-Metric-Space
      ( A)
      ( A)
      ( comp-isometry-Metric-Space A B A isometric-inv f)
      ( isometry-id-Metric-Space A)
      ( is-retraction-map-inv-is-equiv is-equiv-f))
    where

    is-equiv-f : is-equiv (map-isometry-Metric-Space A B f)
    is-equiv-f =
      is-equiv-is-iso-precategory-short-function-Metric-Space
        ( A)
        ( B)
        ( short-isometry-Metric-Space A B f)
        ( H)

    isometric-inv : isometry-Metric-Space B A
    isometric-inv =
      isometry-inv-is-equiv-is-isometry-Metric-Space
        ( A)
        ( B)
        ( map-isometry-Metric-Space A B f)
        ( is-equiv-f)
        ( is-isometry-map-isometry-Metric-Space A B f)
```
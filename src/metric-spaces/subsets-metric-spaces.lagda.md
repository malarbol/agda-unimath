# Subsets of metric spaces

```agda
module metric-spaces.subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.uniform-continuity-functions-metric-spaces
```

</details>

## Idea

Subsets of metric spaces inherit the metric structure of their ambient space.
Moreover, the natural inclusion is uniformly continuous.

## Definitions

```agda
module _
  (l : Level) {l1 : Level} (A : Metric-Space l1)
  where

  subset-Metric-Space : UU (lsuc l ⊔ l1)
  subset-Metric-Space = subtype l (type-Metric-Space A)
```

```agda
module _
  {l : Level} (A : Metric-Space l) (S : subset-Metric-Space l A)
  where

  set-subset-Metric-Space : Set l
  set-subset-Metric-Space = set-subset (set-Metric-Space A) S

  substructure-Metric-Space : Metric-Structure l set-subset-Metric-Space
  pr1 substructure-Metric-Space d x y =
    neighbourhood-Metric-Space A d (pr1 x) (pr1 y)
  pr2 substructure-Metric-Space =
    ( λ d x y → is-symmetric-neighbourhood-Metric-Space A d (pr1 x) (pr1 y)) ,
    ( λ d x → is-reflexive-neighbourhood-Metric-Space A d (pr1 x)) ,
    ( λ x y H →
      eq-type-subtype S
        (is-tight-neighbourhood-Metric-Space A (pr1 x) (pr1 y) H)) ,
    ( λ x y z →
      is-triangular-neighbourhood-Metric-Space A (pr1 x) (pr1 y) (pr1 z))

  subspace-Metric-Space : Metric-Space l
  subspace-Metric-Space = (set-subset-Metric-Space , substructure-Metric-Space)

  inclusion-subspace-Metric-Space : fun-Metric-Space subspace-Metric-Space A
  inclusion-subspace-Metric-Space x = pr1 x

  is-uniformly-continuous-inclusion-subspace-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space
      subspace-Metric-Space
      A
      inclusion-subspace-Metric-Space
  is-uniformly-continuous-inclusion-subspace-Metric-Space ε = (ε , λ x y H → H)
```

## Properties

### Open subsets of metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (S : subset-Metric-Space l2 A)
  where

    is-open-subset-Metric-Space : UU (l1 ⊔ l2)
    is-open-subset-Metric-Space =
      (x : type-Metric-Space A) →
      ( is-in-subtype S x) →
      Σ ℚ⁺
        ( λ d →
          ( y : type-Metric-Space A) →
          ( is-in-neighbourhood-Metric-Space A d x y) →
          ( is-in-subtype S y))
```

# Bisequential diagrams of isometries between metric spaces

```agda
module metric-spaces.bisequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.morphisms-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.sequential-diagrams-isometries-metric-spaces

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "bisequential diagram" Disambiguation="of isometries between metric spaces" Agda=bisequential-diagram-isometry-Metric-Space}}
is a [sequence](lists.sequences.md) of
[diagrams](metric-spaces.sequential-diagrams-isometries-metric-spaces.md) of
[isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) equipped with a sequence of
[morphisms](metric-spaces.morphisms-sequential-diagrams-isometries-metric-spaces.md)
between each successive row.

These can be thought as diagrams of metric spaces and isometries

```text
  M₀⁰ ----> M₀¹ ----> M₀² ----> ... ----> M₀ʲ ----> ...
   |         |        |                    |
   |         |        |                    |
   V         v        v                    v
  M₁⁰ ----> M₁¹ ----> M₁² ----> ...      .....
   |         |        |
   |         |        |
   v         v        v
  M₂⁰ ----> M₂¹ --> ..... ----> ...        .
   .         .        .                    .
   .         .        .                    .
   .         .        .                    .
   v         v        v                    v
  Mᵢ⁰ ----> Mᵢ¹ --> ..... ----> ... ----> Mᵢʲ ----> ...
   .         .        .                    .
   .         .        .                    .
   .         .        .                    .
```

extending infinitely to the right and the bottom, such that all subsquare
diagrams [commute](foundation.commuting-squares-of-maps.md).

## Definitions

### The type of bisequential diagrams of isometries

```agda
module _
  (l1 l2 : Level)
  where

  bisequential-diagram-isometry-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  bisequential-diagram-isometry-Metric-Space =
    Σ ( (n : ℕ) → sequential-diagram-isometry-Metric-Space l1 l2)
      ( λ M →
        (i : ℕ) →
        hom-sequential-diagram-isometry-Metric-Space (M i) (M (succ-ℕ i)))
```

### Components of a bisequential diagram of isometries

```agda
module _
  {l1 l2 : Level}
  (M : bisequential-diagram-isometry-Metric-Space l1 l2)
  where

  seq-row-bisequential-diagram-isometry-Metric-Space :
    (i : ℕ) → sequential-diagram-isometry-Metric-Space l1 l2
  seq-row-bisequential-diagram-isometry-Metric-Space = pr1 M

  seq-hom-row-bisequential-diagram-isometry-Metric-Space :
    (i : ℕ) →
    hom-sequential-diagram-isometry-Metric-Space
      ( seq-row-bisequential-diagram-isometry-Metric-Space i)
      ( seq-row-bisequential-diagram-isometry-Metric-Space (succ-ℕ i))
  seq-hom-row-bisequential-diagram-isometry-Metric-Space = pr2 M

  biseq-metric-space-bisequential-diagram-isometry-Metric-Space :
    (i j : ℕ) → Metric-Space l1 l2
  biseq-metric-space-bisequential-diagram-isometry-Metric-Space i =
    seq-metric-space-sequential-diagram-isometry-Metric-Space
      ( seq-row-bisequential-diagram-isometry-Metric-Space i)

  row-isometry-bisequential-diagram-isometry-Metric-Space :
    (i j : ℕ) →
    isometry-Metric-Space
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space i j)
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
        ( i)
        ( succ-ℕ j))
  row-isometry-bisequential-diagram-isometry-Metric-Space i =
    seq-isometry-sequential-diagram-isometry-Metric-Space
      ( seq-row-bisequential-diagram-isometry-Metric-Space i)

  col-isometry-bisequential-diagram-isometry-Metric-Space :
    (i j : ℕ) →
    isometry-Metric-Space
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space i j)
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
        ( succ-ℕ i)
        ( j))
  col-isometry-bisequential-diagram-isometry-Metric-Space i =
    seq-isometry-hom-sequential-diagram-isometry-Metric-Space
      ( seq-row-bisequential-diagram-isometry-Metric-Space i)
      ( seq-row-bisequential-diagram-isometry-Metric-Space (succ-ℕ i))
      ( seq-hom-row-bisequential-diagram-isometry-Metric-Space i)

  coh-square-isometry-bisequential-diagram-isometry-Metric-Space :
    (i j : ℕ) →
    htpy-map-isometry-Metric-Space
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space i j)
      ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
        ( succ-ℕ i)
        ( succ-ℕ j))
      ( comp-isometry-Metric-Space
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space i j)
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
          ( succ-ℕ i)
          ( j))
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
          ( succ-ℕ i)
          ( succ-ℕ j))
        ( row-isometry-bisequential-diagram-isometry-Metric-Space (succ-ℕ i) j)
        ( col-isometry-bisequential-diagram-isometry-Metric-Space i j))
      ( comp-isometry-Metric-Space
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space i j)
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
          ( i)
          ( succ-ℕ j))
        ( biseq-metric-space-bisequential-diagram-isometry-Metric-Space
          ( succ-ℕ i)
          ( succ-ℕ j))
        ( col-isometry-bisequential-diagram-isometry-Metric-Space i (succ-ℕ j))
        ( row-isometry-bisequential-diagram-isometry-Metric-Space i j))
  coh-square-isometry-bisequential-diagram-isometry-Metric-Space i j =
    naturality-seq-isometry-hom-sequential-diagram-isometry-Metric-Space
      ( seq-row-bisequential-diagram-isometry-Metric-Space i)
      ( seq-row-bisequential-diagram-isometry-Metric-Space (succ-ℕ i))
      ( seq-hom-row-bisequential-diagram-isometry-Metric-Space i)
      ( j)
```

### The columns of a bisequential diagram

```agda
module _
  {l1 l2 : Level}
  (M : bisequential-diagram-isometry-Metric-Space l1 l2)
  where

  seq-col-bisequential-diagram-isometry-Metric-Space :
    (j : ℕ) → sequential-diagram-isometry-Metric-Space l1 l2
  seq-col-bisequential-diagram-isometry-Metric-Space j =
    ( ( λ i →
        biseq-metric-space-bisequential-diagram-isometry-Metric-Space M i j) ,
      ( λ i → col-isometry-bisequential-diagram-isometry-Metric-Space M i j))

  seq-hom-col-bisequential-diagram-isometry-Metric-Space :
    (j : ℕ) →
    hom-sequential-diagram-isometry-Metric-Space
      ( seq-col-bisequential-diagram-isometry-Metric-Space j)
      ( seq-col-bisequential-diagram-isometry-Metric-Space (succ-ℕ j))
  seq-hom-col-bisequential-diagram-isometry-Metric-Space j =
    ( ( λ i → row-isometry-bisequential-diagram-isometry-Metric-Space M i j) ,
      ( λ i →
        inv-htpy
          ( coh-square-isometry-bisequential-diagram-isometry-Metric-Space
            ( M)
            ( i)
            ( j))))
```

### Transposing bisequential diagrams of isometries

```agda
module _
  {l1 l2 : Level}
  (M : bisequential-diagram-isometry-Metric-Space l1 l2)
  where

  transpose-bisequential-diagram-isometry-Metric-Space :
    bisequential-diagram-isometry-Metric-Space l1 l2
  transpose-bisequential-diagram-isometry-Metric-Space =
    ( seq-col-bisequential-diagram-isometry-Metric-Space M ,
      seq-hom-col-bisequential-diagram-isometry-Metric-Space M)
```

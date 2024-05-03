# Sequences in metric spaces

```agda
module metric-spaces.sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

Sequences in metric spaces are sequences in the underlyng types.

## Definitions

### Sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  Sequence-Metric-Space : UU l1
  Sequence-Metric-Space = ℕ → type-Metric-Space M
```

### Constant sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (x : type-Metric-Space M)
  where

  constant-Sequence-Metric-Space : Sequence-Metric-Space M
  constant-Sequence-Metric-Space n = x
```

# Continuity of functions between metric spaces

```agda
module metric-spaces.continuity-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.convergent-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Continuity of functions between metric spaces

## Definitions

### Functions between metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  where

  fun-Metric-Space : UU (l1 ⊔ l2)
  fun-Metric-Space = type-Metric-Space A → type-Metric-Space B
```

### Pointwise continuity

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (x : type-Metric-Space A)
  where

  is-pointwise-continuity-modulus-fun-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-pointwise-continuity-modulus-fun-Metric-Space ε δ =
    (y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-pointwise-continuous-fun-Metric-Space : UU (l1 ⊔ l2)
  is-pointwise-continuous-fun-Metric-Space =
    (ε : ℚ⁺) → Σ ℚ⁺ (is-pointwise-continuity-modulus-fun-Metric-Space ε)

module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (x : type-Metric-Space A)
  (H : is-pointwise-continuous-fun-Metric-Space A B f x)
  where

  pt-continuity-modulus-fun-Metric-Space : ℚ⁺ → ℚ⁺
  pt-continuity-modulus-fun-Metric-Space ε = pr1 (H ε)

  is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space :
    (ε : ℚ⁺) →
    is-pointwise-continuity-modulus-fun-Metric-Space A B f x ε
      (pt-continuity-modulus-fun-Metric-Space ε)
  is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space ε =
    pr2 (H ε)
```

### Uniform continuity

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  where

  is-continuity-modulus-fun-Metric-Space : ℚ⁺ → ℚ⁺ → UU (l1 ⊔ l2)
  is-continuity-modulus-fun-Metric-Space ε δ =
    (x y : type-Metric-Space A) →
    is-in-neighbourhood-Metric-Space A δ x y →
    is-in-neighbourhood-Metric-Space B ε (f x) (f y)

  is-uniformly-continuous-fun-Metric-Space : UU (l1 ⊔ l2)
  is-uniformly-continuous-fun-Metric-Space =
    (ε : ℚ⁺) → Σ ℚ⁺ (is-continuity-modulus-fun-Metric-Space ε)

module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  (H : is-uniformly-continuous-fun-Metric-Space A B f) (ε : ℚ⁺)
  where

  continuity-modulus-fun-Metric-Space : ℚ⁺
  continuity-modulus-fun-Metric-Space = pr1 (H ε)

  is-continuity-modulus-continuity-modulus-fun-Metric-Space :
    is-continuity-modulus-fun-Metric-Space A B f ε
      continuity-modulus-fun-Metric-Space
  is-continuity-modulus-continuity-modulus-fun-Metric-Space = pr2 (H ε)
```

## Properties

### Uniformly continuous functions are continuous at every points

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B)
  where

  is-continuous-is-uniformly-continuous-fun-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space A B f →
    (x : type-Metric-Space A) →
    is-pointwise-continuous-fun-Metric-Space A B f x
  is-continuous-is-uniformly-continuous-fun-Metric-Space H x ε =
    ( continuity-modulus-fun-Metric-Space A B f H ε) ,
    ( is-continuity-modulus-continuity-modulus-fun-Metric-Space A B f H ε x)
```

### The identity function is uniformly continuous

```agda
module _
  {l : Level} (A : Metric-Space l)
  where

  is-uniformly-continuous-id-Metric-Space :
    is-uniformly-continuous-fun-Metric-Space A A id
  is-uniformly-continuous-id-Metric-Space ε = ε , λ x y H → H
```

### The image of a convergent sequence by a function continuous at the limit point converges to the image of the limit point

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1) (B : Metric-Space l2)
  (f : fun-Metric-Space A B) (u : Convergent-Sequence-Metric-Space A)
  where

  is-convergent-pointwise-continuous-map-Convergent-Sequence-Metric-Space :
    is-pointwise-continuous-fun-Metric-Space A B f
      ( limit-Convergent-Sequence-Metric-Space A u) →
    is-limit-Sequence-Metric-Space B
      ( map-sequence f (sequence-Convergent-Sequence-Metric-Space A u))
      ( f (limit-Convergent-Sequence-Metric-Space A u))
  is-convergent-pointwise-continuous-map-Convergent-Sequence-Metric-Space H d =
    ( modulus-limit-Sequence-Metric-Space A
      ( sequence-Convergent-Sequence-Metric-Space A u)
      ( limit-Convergent-Sequence-Metric-Space A u)
      ( is-limit-Convergent-Sequence-Metric-Space A u)
      ( pt-continuity-modulus-fun-Metric-Space A B f
        ( limit-Convergent-Sequence-Metric-Space A u)
        ( H)
        ( d))) ,
    ( λ n K →
      is-pointwise-continuity-modulus-pt-continuity-modulus-fun-Metric-Space
        ( A)
        ( B)
        ( f)
        ( limit-Convergent-Sequence-Metric-Space A u)
        ( H)
        ( d)
        ( sequence-Convergent-Sequence-Metric-Space A u n)
        ( is-modulus-modulus-limit-Sequence-Metric-Space A
          ( sequence-Convergent-Sequence-Metric-Space A u)
          ( limit-Convergent-Sequence-Metric-Space A u)
          ( is-limit-Convergent-Sequence-Metric-Space A u)
          ( pt-continuity-modulus-fun-Metric-Space A B f
            ( limit-Convergent-Sequence-Metric-Space A u)
            ( H)
            ( d))
          ( n)
          ( K)))
```

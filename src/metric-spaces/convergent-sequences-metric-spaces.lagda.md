# Convergent sequences in metric spaces

```agda
module metric-spaces.convergent-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.monotonic-endomaps-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.asymptotically-constant-sequences
open import foundation.asymptotically-equal-sequences
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subsequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.neighbourhood-relations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

Convergent sequences in metric spaces are sequences that have a limit.

## Definitions

### Limits of sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  is-modulus-limit-prop-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → Prop l
  is-modulus-limit-prop-Sequence-Metric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        hom-Prop (leq-ℕ-Prop N n) (neighbourhood-Metric-Space M d x (u n)))

  is-modulus-limit-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → UU l
  is-modulus-limit-Sequence-Metric-Space d N =
    type-Prop (is-modulus-limit-prop-Sequence-Metric-Space d N)

  is-limit-Sequence-Metric-Space : UU l
  is-limit-Sequence-Metric-Space =
    (d : ℚ⁺) → Σ ℕ (is-modulus-limit-Sequence-Metric-Space d)

  modulus-limit-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-limit-Sequence-Metric-Space H d = pr1 (H d)

  is-modulus-modulus-limit-Sequence-Metric-Space :
    (H : is-limit-Sequence-Metric-Space) (d : ℚ⁺) →
    is-modulus-limit-Sequence-Metric-Space
      ( d)
      ( modulus-limit-Sequence-Metric-Space H d)
  is-modulus-modulus-limit-Sequence-Metric-Space H d = pr2 (H d)
```

### Convergent sequences in metric spaces

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  is-convergent-Sequence-Metric-Space : (u : Sequence-Metric-Space M) → UU l
  is-convergent-Sequence-Metric-Space u =
    Σ (type-Metric-Space M) (is-limit-Sequence-Metric-Space M u)
```

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (H : is-convergent-Sequence-Metric-Space M u)
  where

  limit-Sequence-Metric-Space : type-Metric-Space M
  limit-Sequence-Metric-Space = pr1 H

  is-limit-limit-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space M u limit-Sequence-Metric-Space
  is-limit-limit-Sequence-Metric-Space = pr2 H
```

```agda
module _
  {l : Level} (M : Metric-Space l)
  where

  Convergent-Sequence-Metric-Space : UU l
  Convergent-Sequence-Metric-Space =
    Σ (Sequence-Metric-Space M) (is-convergent-Sequence-Metric-Space M)

module _
  {l : Level} (M : Metric-Space l) (u : Convergent-Sequence-Metric-Space M)
  where

  sequence-Convergent-Sequence-Metric-Space : Sequence-Metric-Space M
  sequence-Convergent-Sequence-Metric-Space = pr1 u

  limit-Convergent-Sequence-Metric-Space : type-Metric-Space M
  limit-Convergent-Sequence-Metric-Space = pr1 (pr2 u)

  is-limit-Convergent-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space M
      sequence-Convergent-Sequence-Metric-Space
      limit-Convergent-Sequence-Metric-Space
  is-limit-Convergent-Sequence-Metric-Space = pr2 (pr2 u)

  modulus-Convergent-Sequence-Metric-Space : ℚ⁺ → ℕ
  modulus-Convergent-Sequence-Metric-Space =
    modulus-limit-Sequence-Metric-Space M
      sequence-Convergent-Sequence-Metric-Space
      limit-Convergent-Sequence-Metric-Space
      is-limit-Convergent-Sequence-Metric-Space

  is-modulus-modulus-Convergent-Sequence-Metric-Space :
    (d : ℚ⁺) →
    is-modulus-limit-Sequence-Metric-Space M
      ( sequence-Convergent-Sequence-Metric-Space)
      ( limit-Convergent-Sequence-Metric-Space)
      ( d)
      ( modulus-Convergent-Sequence-Metric-Space d)
  is-modulus-modulus-Convergent-Sequence-Metric-Space =
    is-modulus-modulus-limit-Sequence-Metric-Space M
      ( sequence-Convergent-Sequence-Metric-Space)
      ( limit-Convergent-Sequence-Metric-Space)
      ( is-limit-Convergent-Sequence-Metric-Space)
```

## Properties

### Two limits of a sequence in a metric space are indistinguishable

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (x y : type-Metric-Space M)
  where

  indistinguishable-limit-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space M u x →
    is-limit-Sequence-Metric-Space M u y →
    is-indistinguishable-Neighbourhood
      ( neighbourhood-Metric-Space M)
      ( x)
      ( y)
  indistinguishable-limit-Sequence-Metric-Space H K d =
    tr
      ( λ d' → is-in-neighbourhood-Metric-Space M d' x y)
      ( left-diff-law-add-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d))
      ( is-triangular-neighbourhood-Metric-Space M
        ( x)
        ( u N)
        ( y)
        ( d₁)
        ( d₂)
        ( is-symmetric-neighbourhood-Metric-Space M d₂ y (u N) β)
        ( α))
    where
      d₂ : ℚ⁺
      d₂ = mediant-zero-ℚ⁺ d

      d₁ : ℚ⁺
      d₁ = le-diff-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d)

      Nx : ℕ
      Nx = modulus-limit-Sequence-Metric-Space M u x H d₁

      Ny : ℕ
      Ny = modulus-limit-Sequence-Metric-Space M u y K d₂

      N : ℕ
      N = max-ℕ Nx Ny

      α : is-in-neighbourhood-Metric-Space M d₁ x (u N)
      α =
        is-modulus-modulus-limit-Sequence-Metric-Space M u x H d₁ N
          (leq-left-leq-max-ℕ N Nx Ny (refl-leq-ℕ N))

      β : is-in-neighbourhood-Metric-Space M d₂ y (u N)
      β =
        is-modulus-modulus-limit-Sequence-Metric-Space M u y K d₂ N
          (leq-right-leq-max-ℕ N Nx Ny (refl-leq-ℕ N))
```

### Two limits of a sequence in a metric space are equal

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (x y : type-Metric-Space M)
  where

  eq-limit-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space M u x →
    is-limit-Sequence-Metric-Space M u y →
    x ＝ y
  eq-limit-Sequence-Metric-Space H K =
    is-tight-neighbourhood-Metric-Space M x y
      (indistinguishable-limit-Sequence-Metric-Space M u x y H K)
```

### Constant sequences in metric spaces are convergent

```agda
module _
  {l : Level} (M : Metric-Space l) (x : type-Metric-Space M)
  where

  is-limit-constant-Sequence-Metric-Space :
    is-limit-Sequence-Metric-Space M (λ n → x) x
  is-limit-constant-Sequence-Metric-Space d =
    (zero-ℕ , λ n H → is-reflexive-neighbourhood-Metric-Space M d x)

  is-convergent-constant-Sequence-Metric-Space :
    is-convergent-Sequence-Metric-Space M (λ n → x)
  is-convergent-constant-Sequence-Metric-Space =
    (x , is-limit-constant-Sequence-Metric-Space)
```

### Asymptotical equality preserves limits

```agda
module _
  {l : Level} (M : Metric-Space l) (u v : Sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  preserves-limit-eq-∞-Sequence-Metric-Space :
    eq-∞-sequence u v →
    is-limit-Sequence-Metric-Space M u x →
    is-limit-Sequence-Metric-Space M v x
  pr1 (preserves-limit-eq-∞-Sequence-Metric-Space I H d) =
      max-ℕ (pr1 I) (modulus-limit-Sequence-Metric-Space M u x H d)
  pr2 (preserves-limit-eq-∞-Sequence-Metric-Space I H d) n K =
    tr
      ( is-in-neighbourhood-Metric-Space M d x)
      ( pr2 I n
        ( leq-left-leq-max-ℕ
          ( n)
          ( pr1 I)
          ( modulus-limit-Sequence-Metric-Space M u x H d)
          ( K)))
      ( is-modulus-modulus-limit-Sequence-Metric-Space M u x H d n
        ( leq-right-leq-max-ℕ
          ( n)
          ( pr1 I)
          ( modulus-limit-Sequence-Metric-Space M u x H d)
          ( K)))
```

### A subsequence of a convergent sequence converges to the same limit

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  preserves-limit-subsequence-Metric-Space :
    (v : subsequence u) →
    is-limit-Sequence-Metric-Space M u x →
    is-limit-Sequence-Metric-Space M (sequence-subsequence u v) x
  preserves-limit-subsequence-Metric-Space v H d =
    map-Σ
      ( is-modulus-limit-Sequence-Metric-Space M
        ( sequence-subsequence u v) x d)
      ( modulus-limit-∞-is-strictly-increasing-endomap-ℕ
        ( extract-subsequence u v)
        ( is-strictly-increasing-extract-subsequence u v))
      ( λ N K p I →
        K
          ( extract-subsequence u v p)
          ( is-modulus-modulus-limit-∞-is-strictly-increasing-endomap-ℕ
            ( extract-subsequence u v)
            ( is-strictly-increasing-extract-subsequence u v)
            ( N)
            ( p)
            ( I)))
      ( H d)
```

### A sequence has a limit if all its subsequences have this limit

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  reflects-limit-subsequence-Metric-Space :
    ( ( v : subsequence u) →
      ( is-limit-Sequence-Metric-Space M
        ( sequence-subsequence u v)
        ( x))) →
    is-limit-Sequence-Metric-Space M u x
  reflects-limit-subsequence-Metric-Space H = H (refl-subsequence u)
```

### Asymptotically constant sequences in metric spaces converge to their asymptotical value

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  where

  is-limit-∞-value-∞-constant-Sequence-Metric-Space :
    (H : is-∞-constant-sequence u) →
    is-limit-Sequence-Metric-Space M u (∞-value-∞-constant-sequence u H)
  is-limit-∞-value-∞-constant-Sequence-Metric-Space H =
    ( preserves-limit-eq-∞-Sequence-Metric-Space M
      ( λ n → ∞-value-∞-constant-sequence u H)
      ( u)
      ( ∞-value-∞-constant-sequence u H)
      ( eq-∞-constant-sequence u H)
      ( is-limit-constant-Sequence-Metric-Space M
        ( ∞-value-∞-constant-sequence u H)))
```

### Asymptotically constant sequences in metric spaces are convergent

```agda
module _
  {l : Level} (M : Metric-Space l) (u : Sequence-Metric-Space M)
  where

  is-convergent-is-∞-constant-Sequence-Metric-Space :
    is-∞-constant-sequence u →
    is-convergent-Sequence-Metric-Space M u
  is-convergent-is-∞-constant-Sequence-Metric-Space H =
    ( ∞-value-∞-constant-sequence u H) ,
    ( is-limit-∞-value-∞-constant-Sequence-Metric-Space M u H)
```

### Convergent sequences in discrete metric spaces are asymptotically constant

```agda
module _
  {l : Level} {A : Set l} (u : sequence (type-Set A))
  where

  is-∞-constant-is-convergent-Sequence-discrete-Metric-Space :
    is-convergent-Sequence-Metric-Space
      (discrete-Metric-Space A)
      ( u) →
    is-∞-constant-sequence u
  pr1 (is-∞-constant-is-convergent-Sequence-discrete-Metric-Space H) =
    modulus-limit-Sequence-Metric-Space
      ( discrete-Metric-Space A)
      ( u)
      ( limit-Sequence-Metric-Space
        ( discrete-Metric-Space A)
        ( u)
        ( H))
      ( is-limit-limit-Sequence-Metric-Space (discrete-Metric-Space A) u H)
      ( one-ℚ⁺)
  pr2 (is-∞-constant-is-convergent-Sequence-discrete-Metric-Space H) p q I J =
    (inv α) ∙ β
    where

    α :
      Id
        ( limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( u p)
    α =
      is-modulus-modulus-limit-Sequence-Metric-Space
        ( discrete-Metric-Space A)
        ( u)
        ( limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( is-limit-limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( one-ℚ⁺)
        ( p)
        ( I)

    β :
      Id
        ( limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( u q)
    β =
      is-modulus-modulus-limit-Sequence-Metric-Space
        ( discrete-Metric-Space A)
        ( u)
        ( limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( is-limit-limit-Sequence-Metric-Space
          ( discrete-Metric-Space A)
          ( u)
          ( H))
        ( one-ℚ⁺)
        ( q)
        ( J)
```

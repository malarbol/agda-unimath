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

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  Sequence-Metric-Space : UU l1
  Sequence-Metric-Space = ℕ → type-Metric-Space M
```

## Properties

### Limits of sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
  (x : type-Metric-Space M)
  where

  is-modulus-limit-prop-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → Prop l2
  is-modulus-limit-prop-Sequence-Metric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        hom-Prop (leq-ℕ-Prop N n) (neighbourhood-Metric-Space M d x (u n)))

  is-modulus-limit-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-limit-Sequence-Metric-Space d N =
    type-Prop (is-modulus-limit-prop-Sequence-Metric-Space d N)

  is-limit-Sequence-Metric-Space : UU l2
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

### Two limits of a sequence in a metric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
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
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
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

### Convergent sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
  where

  is-convergent-Sequence-Metric-Space : UU (l1 ⊔ l2)
  is-convergent-Sequence-Metric-Space =
    Σ (type-Metric-Space M) (is-limit-Sequence-Metric-Space M u)
```

### Constant sequences in metric spaces are convergent

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (x : type-Metric-Space M)
  where

  is-convergent-constant-Sequence-Metric-Space :
    is-convergent-Sequence-Metric-Space M (λ n → x)
  pr1 is-convergent-constant-Sequence-Metric-Space = x
  pr2 is-convergent-constant-Sequence-Metric-Space d =
    ( zero-ℕ , λ n H → is-reflexive-neighbourhood-Metric-Space M d x)
```

### Cauchy sequences in metric spaces

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
  where

  is-modulus-cauchy-prop-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → Prop l2
  is-modulus-cauchy-prop-Sequence-Metric-Space d N =
    Π-Prop
      ( ℕ)
      ( λ (n : ℕ) →
        ( Π-Prop
          ( ℕ)
          ( λ (m : ℕ) →
            hom-Prop
              ( leq-ℕ-Prop N n)
              ( hom-Prop
                ( leq-ℕ-Prop N m)
                ( neighbourhood-Metric-Space M d (u n) (u m))))))

  is-modulus-cauchy-Sequence-Metric-Space : (d : ℚ⁺) (N : ℕ) → UU l2
  is-modulus-cauchy-Sequence-Metric-Space d N =
    type-Prop (is-modulus-cauchy-prop-Sequence-Metric-Space d N)

  is-cauchy-Sequence-Metric-Space : UU l2
  is-cauchy-Sequence-Metric-Space =
    (d : ℚ⁺) → Σ ℕ (is-modulus-cauchy-Sequence-Metric-Space d)
```

### Convergent sequences in metric spaces are Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2) (u : Sequence-Metric-Space M)
  where

  is-cauchy-is-convergent-Sequence-Metric-Space :
    is-convergent-Sequence-Metric-Space M u →
    is-cauchy-Sequence-Metric-Space M u
  is-cauchy-is-convergent-Sequence-Metric-Space (x , H) d = (N , α)
    where
      d₂ : ℚ⁺
      d₂ = mediant-zero-ℚ⁺ d

      d₁ : ℚ⁺
      d₁ = le-diff-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d)

      Np : ℕ
      Np = modulus-limit-Sequence-Metric-Space M u x H d₁

      Nq : ℕ
      Nq = modulus-limit-Sequence-Metric-Space M u x H d₂

      N : ℕ
      N = max-ℕ Np Nq

      α : is-modulus-cauchy-Sequence-Metric-Space M u d N
      α p q I J =
        tr
          ( λ d' → is-in-neighbourhood-Metric-Space M d' (u p) (u q))
          ( left-diff-law-add-ℚ⁺ d₂ d (le-mediant-zero-ℚ⁺ d))
          ( is-triangular-neighbourhood-Metric-Space M
            ( u p)
            ( x)
            ( u q)
            ( d₁)
            ( d₂)
            ( γ)
            ( is-symmetric-neighbourhood-Metric-Space M d₁ x (u p) β))
        where
          β : is-in-neighbourhood-Metric-Space M d₁ x (u p)
          β =
            is-modulus-modulus-limit-Sequence-Metric-Space M u x H d₁ p
              ( transitive-leq-ℕ Np N p I
                ( leq-left-leq-max-ℕ N Np Nq (refl-leq-ℕ N)))

          γ : is-in-neighbourhood-Metric-Space M d₂ x (u q)
          γ =
            is-modulus-modulus-limit-Sequence-Metric-Space M u x H d₂ q
              ( transitive-leq-ℕ Nq N q J
                ( leq-right-leq-max-ℕ N Np Nq (refl-leq-ℕ N)))
```
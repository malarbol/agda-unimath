# Strict inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="real numbers" Agda=le-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
presence of a [rational number](elementary-number-theory.rational-numbers.md)
between them. This is the definition used in {{#cite UF13}}, section 11.2.1.

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  le-ℝ-Prop : Prop (l1 ⊔ l2)
  le-ℝ-Prop = ∃ ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

  le-ℝ : UU (l1 ⊔ l2)
  le-ℝ = type-Prop le-ℝ-Prop

  is-prop-le-ℝ : is-prop le-ℝ
  is-prop-le-ℝ = is-prop-type-Prop le-ℝ-Prop
```

## Properties

### Strict inequality on the reals is irreflexive

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  irreflexive-le-ℝ : ¬ (le-ℝ x x)
  irreflexive-le-ℝ =
    elim-exists
      ( empty-Prop)
      ( λ q (q-in-ux , q-in-lx) → is-disjoint-cut-ℝ x q (q-in-lx , q-in-ux))
```

### Strict inequality on the reals is asymmetric

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  asymmetric-le-ℝ : le-ℝ x y → ¬ (le-ℝ y x)
  asymmetric-le-ℝ x<y y<x =
    elim-exists
      ( empty-Prop)
      ( λ p (p-in-ux , p-in-ly) →
        elim-exists
          ( empty-Prop)
          ( λ q (q-in-uy , q-in-lx) →
            rec-coproduct
              ( λ p<q →
                asymmetric-le-ℚ
                  ( p)
                  ( q)
                  ( p<q)
                  ( le-lower-upper-cut-ℝ x q p q-in-lx p-in-ux))
              ( λ q≤p →
                not-leq-le-ℚ
                  ( p)
                  ( q)
                  ( le-lower-upper-cut-ℝ y p q p-in-ly q-in-uy)
                  ( q≤p))
              ( decide-le-leq-ℚ p q))
          ( y<x))
      ( x<y)
```

### Strict inequality on the reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-le-ℝ : le-ℝ y z → le-ℝ x y → le-ℝ x z
  transitive-le-ℝ y<z =
    elim-exists
      ( le-ℝ-Prop x z)
      ( λ p (p-in-ux , p-in-ly) →
        elim-exists
          (le-ℝ-Prop x z)
          (λ q (q-in-uy , q-in-lz) →
            intro-exists
              p
              ( p-in-ux ,
                le-lower-cut-ℝ
                  ( z)
                  ( p)
                  ( q)
                  ( le-lower-upper-cut-ℝ y p q p-in-ly q-in-uy)
                  ( q-in-lz)))
          ( y<z))
```

### The canonical map from rationals to reals preserves and reflects strict inequality

```agda
module _
  (x y : ℚ)
  where

  preserves-le-real-ℚ : le-ℚ x y → le-ℝ (real-ℚ x) (real-ℚ y)
  preserves-le-real-ℚ x<y =
    intro-exists
      ( mediant-ℚ x y)
      ( le-left-mediant-ℚ x y x<y , le-right-mediant-ℚ x y x<y)

  reflects-le-real-ℚ : le-ℝ (real-ℚ x) (real-ℚ y) → le-ℚ x y
  reflects-le-real-ℚ =
    elim-exists
      ( le-ℚ-Prop x y)
      ( λ q (x<q , q<y) → transitive-le-ℚ x q y q<y x<q)

  iff-le-real-ℚ : le-ℚ x y ↔ le-ℝ (real-ℚ x) (real-ℚ y)
  pr1 iff-le-real-ℚ = preserves-le-real-ℚ
  pr2 iff-le-real-ℚ = reflects-le-real-ℚ
```

### Concatenation rules for inequality and strict inequality on the real numbers

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  concatenate-le-leq-ℝ : le-ℝ x y → leq-ℝ y z → le-ℝ x z
  concatenate-le-leq-ℝ x<y y≤z =
    elim-exists
      ( le-ℝ-Prop x z)
      ( λ p (p-in-upper-x , p-in-lower-y) →
        intro-exists p (p-in-upper-x , y≤z p p-in-lower-y))
      ( x<y)

  concatenate-leq-le-ℝ : leq-ℝ x y → le-ℝ y z → le-ℝ x z
  concatenate-leq-le-ℝ x≤y y<z =
    elim-exists
      ( le-ℝ-Prop x z)
      ( λ p (p-in-upper-y , p-in-lower-z) →
        intro-exists
          ( p)
          ( forward-implication
            ( leq-iff-ℝ' x y)
            ( x≤y)
            ( p)
            ( p-in-upper-y) ,
        p-in-lower-z))
      ( y<z)
```

### The reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  exists-lesser-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop y x)
  exists-lesser-ℝ =
    elim-exists
      ( ∃ (ℝ lzero) (λ y → le-ℝ-Prop y x))
      ( λ q q-in-lx →
        intro-exists
          ( real-ℚ q)
          ( forward-implication (is-rounded-lower-cut-ℝ x q) q-in-lx))
      ( is-inhabited-lower-cut-ℝ x)

  exists-greater-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop x y)
  exists-greater-ℝ =
    elim-exists
      ( ∃ (ℝ lzero) (λ y → le-ℝ-Prop x y))
      ( λ q q-in-ux →
        intro-exists
          ( real-ℚ q)
          ( elim-exists
              ( le-ℝ-Prop x (real-ℚ q))
              ( λ r (r<q , r-in-ux) → intro-exists r (r-in-ux , r<q))
              ( forward-implication (is-rounded-upper-cut-ℝ x q) q-in-ux)))
      ( is-inhabited-upper-cut-ℝ x)
```

### Negation reverses the strict ordering of real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  reverses-order-neg-ℝ : le-ℝ x y → le-ℝ (neg-ℝ y) (neg-ℝ x)
  reverses-order-neg-ℝ =
    elim-exists
      ( le-ℝ-Prop (neg-ℝ y) (neg-ℝ x))
      ( λ p (p-in-ux , p-in-ly) →
        intro-exists
          ( neg-ℚ p)
          ( tr (is-in-lower-cut-ℝ y) (inv (neg-neg-ℚ p)) p-in-ly ,
            tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ p)) p-in-ux))
```

### If `x` is less than `y`, then `y` is not less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-leq-le-ℝ : le-ℝ x y → ¬ (leq-ℝ y x)
  not-leq-le-ℝ x<y y≤x =
    elim-exists
      ( empty-Prop)
      ( λ q (q-in-ux , q-in-ly) →
        is-disjoint-cut-ℝ x q (y≤x q q-in-ly , q-in-ux))
      ( x<y)
```

### If `x` is not less than `y`, then `y` is less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-not-le-ℝ : ¬ (le-ℝ x y) → leq-ℝ y x
  leq-not-le-ℝ x≮y p p∈ly =
    elim-exists
      ( lower-cut-ℝ x p)
      ( λ q (p<q , q∈ly) →
        elim-disjunction
          ( lower-cut-ℝ x p)
          ( id)
          ( λ q∈ux → ex-falso (x≮y (intro-exists q (q∈ux , q∈ly))))
          ( is-located-lower-upper-cut-ℝ x p q p<q))
      ( forward-implication (is-rounded-lower-cut-ℝ y p) p∈ly)
```

### If `x` is less than or equal to `y`, then `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-le-leq-ℝ : leq-ℝ x y → ¬ (le-ℝ y x)
  not-le-leq-ℝ x≤y y<x = not-leq-le-ℝ y x y<x x≤y
```

### `x` is less than or equal to `y` if and only if `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-iff-not-le-ℝ : leq-ℝ x y ↔ ¬ (le-ℝ y x)
  pr1 leq-iff-not-le-ℝ = not-le-leq-ℝ x y
  pr2 leq-iff-not-le-ℝ = leq-not-le-ℝ y x
```

### A rational is in the lower cut of `x` iff its real projection is less than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  le-iff-lower-cut-real-ℚ : is-in-lower-cut-ℝ x q ↔ le-ℝ (real-ℚ q) x
  le-iff-lower-cut-real-ℚ = is-rounded-lower-cut-ℝ x q

  le-lower-cut-real-ℚ : is-in-lower-cut-ℝ x q → le-ℝ (real-ℚ q) x
  le-lower-cut-real-ℚ = forward-implication le-iff-lower-cut-real-ℚ

  lower-cut-real-le-ℚ : le-ℝ (real-ℚ q) x → is-in-lower-cut-ℝ x q
  lower-cut-real-le-ℚ = backward-implication le-iff-lower-cut-real-ℚ
```

### A rational is in the upper cut of `x` iff its real projection is greater than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  le-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q → le-ℝ x (real-ℚ q)
  le-upper-cut-real-ℚ H =
    map-tot-exists
      ( λ p (p<q , p∈ux) → (p∈ux , p<q))
      ( forward-implication (is-rounded-upper-cut-ℝ x q) H)

  upper-cut-real-le-ℚ : le-ℝ x (real-ℚ q) → is-in-upper-cut-ℝ x q
  upper-cut-real-le-ℚ H =
    backward-implication
      ( is-rounded-upper-cut-ℝ x q)
      ( map-tot-exists (λ _ (p>x , p<q) → (p<q , p>x)) H)

  le-iff-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q ↔ le-ℝ x (real-ℚ q)
  pr1 le-iff-upper-cut-real-ℚ = le-upper-cut-real-ℚ
  pr2 le-iff-upper-cut-real-ℚ = upper-cut-real-le-ℚ
```

### Strict inequality on the real numbers is dense

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  dense-le-ℝ : le-ℝ x y → exists (ℝ lzero) (λ z → le-ℝ-Prop x z ∧ le-ℝ-Prop z y)
  dense-le-ℝ =
    elim-exists
      ( ∃ (ℝ lzero) (λ z → le-ℝ-Prop x z ∧ le-ℝ-Prop z y))
      ( λ q (q∈ux , q∈ly) →
        map-binary-exists
          ( λ z → le-ℝ x z × le-ℝ z y)
          ( λ _ _ → real-ℚ q)
          ( λ p r (p<q , p∈ux) (q<r , r∈ly) →
            intro-exists p (p∈ux , p<q) , intro-exists r (q<r , r∈ly))
          ( forward-implication (is-rounded-upper-cut-ℝ x q) q∈ux)
          ( forward-implication (is-rounded-lower-cut-ℝ y q) q∈ly))
```

## References

{{#bibliography}}

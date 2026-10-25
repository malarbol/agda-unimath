# Cauchy filters on the Dedekind real numbers

```agda
module real-numbers.cauchy-filters-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-filters-metric-spaces
open import metric-spaces.cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-space-of-cauchy-filters-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.expansive-maps-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.local-rational-neighborhood-subtypes-pseudometric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.proper-rational-neighborhood-subtypes
open import metric-spaces.rational-neighborhood-subtypes
open import metric-spaces.saturated-rational-neighborhood-subtypes
open import metric-spaces.short-maps-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.cauchy-filters-rational-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.dense-subsets-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

Cauchy filters on Dedekind real numbers

## Definitions

### The complete metric space of Cauchy filters of Dedkind real numbers

```agda
module _
  (l1 l2 : Level)
  where

  complete-metric-space-cauchy-filter-ℝ :
    Complete-Metric-Space (lsuc l1 ⊔ lsuc l2) (lsuc l1 ⊔ l2)
  complete-metric-space-cauchy-filter-ℝ =
    complete-metric-space-cauchy-filter-Pseudometric-Space
      ( l2)
      ( pseudometric-space-ℝ l1)

  metric-space-cauchy-filter-ℝ : Metric-Space (lsuc l1 ⊔ lsuc l2) (lsuc l1 ⊔ l2)
  metric-space-cauchy-filter-ℝ =
    metric-space-Complete-Metric-Space
      complete-metric-space-cauchy-filter-ℝ

  cauchy-filter-ℝ : UU (lsuc l1 ⊔ lsuc l2)
  cauchy-filter-ℝ = type-Metric-Space metric-space-cauchy-filter-ℝ
```

### Components of Cauchy filters on the Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (V : cauchy-filter-ℝ l1 l2)
  where

  neighborhood-subtype-cauchy-filter-ℝ : ℚ⁺ → ℝ l1 → Prop l2
  neighborhood-subtype-cauchy-filter-ℝ =
    neighborhood-subtype-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-in-cauchy-filter-ℝ : ℚ⁺ → ℝ l1 → UU l2
  is-in-cauchy-filter-ℝ =
    is-in-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-proper-cauchy-filter-ℝ :
    (ε : ℚ⁺) → exists (ℝ l1) (neighborhood-subtype-cauchy-filter-ℝ ε)
  is-proper-cauchy-filter-ℝ =
    is-proper-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-saturated-cauchy-filter-ℝ :
    (ε : ℚ⁺) (p : ℝ l1) →
    ((μ : ℚ⁺) → is-in-cauchy-filter-ℝ (ε +ℚ⁺ μ) p) →
    is-in-cauchy-filter-ℝ ε p
  is-saturated-cauchy-filter-ℝ ε p =
    is-saturated-cauchy-filter-Metric-Space (metric-space-ℝ l1) V (ε , p)

  is-bounded-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℝ l1) →
    is-in-cauchy-filter-ℝ ε p →
    is-in-cauchy-filter-ℝ δ q →
    neighborhood-ℝ l1 (ε +ℚ⁺ δ) p q
  is-bounded-cauchy-filter-ℝ =
    is-bounded-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-enclosing-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℝ l1) →
    is-in-cauchy-filter-ℝ ε p →
    neighborhood-ℝ l1 δ p q →
    is-in-cauchy-filter-ℝ (ε +ℚ⁺ δ) q
  is-enclosing-cauchy-filter-ℝ =
    is-enclosing-cauchy-filter-Metric-Space (metric-space-ℝ l1) V

  is-monotonic-cauchy-filter-ℝ :
    (p : ℝ l1) (ε δ : ℚ⁺) →
    le-ℚ⁺ ε δ →
    is-in-cauchy-filter-ℝ ε p →
    is-in-cauchy-filter-ℝ δ p
  is-monotonic-cauchy-filter-ℝ =
    is-monotonic-cauchy-filter-Metric-Space (metric-space-ℝ l1) V
```

## Properties

### A Cauchy filter on the Dedekind real numbers induces a real number at the same level

```agda
module _
  {l1 l2 : Level} (V : cauchy-filter-ℝ l1 l2)
  where

  neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ :
    Rational-Neighborhood-Subtype l2 ℚ
  neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ε r =
    neighborhood-subtype-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( raise-real-ℚ l1 r)

  is-in-cauchy-filter-ℚ-cauchy-filter-ℝ :
    ℚ⁺ → ℚ → UU l2
  is-in-cauchy-filter-ℚ-cauchy-filter-ℝ =
    is-in-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ

  is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-proper-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ
  is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ ε =
    let
      open
        do-syntax-trunc-Prop
          ( ∃ ℚ (neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ε))
    in do
      (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
      (x , Vx) ← is-proper-cauchy-filter-ℝ V δ
      (p , Nxp) ← exists-rational-approximate-ℝ x δ

      intro-exists
        ( p)
        ( is-monotonic-cauchy-filter-ℝ
          ( V)
          ( raise-real-ℚ l1 p)
          ( δ +ℚ⁺ δ)
          ( ε)
          ( δ+δ<ε)
          ( is-enclosing-cauchy-filter-ℝ
            ( V)
            ( δ)
            ( δ)
            ( x)
            ( raise-real-ℚ l1 p)
            ( Vx)
            ( Nxp)))

  is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-saturated-Rational-Neighborhood-Subtype
      neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ
  is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ
    (ε , p) =
    is-saturated-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( raise-real-ℚ l1 p)

  is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-bounded-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ
    ε δ p q (Vp , Vq) =
    reflects-neighborhoods-map-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l1)
      ( isometry-raise-real-ℚ l1)
      ( ε +ℚ⁺ δ)
      ( p)
      ( q)
      ( is-bounded-cauchy-filter-ℝ
        ( V)
        ( ε)
        ( δ)
        ( raise-real-ℚ l1 p)
        ( raise-real-ℚ l1 q)
        ( Vp)
        ( Vq))

  is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ :
    (ε δ : ℚ⁺) (p q : ℚ) →
    is-enclosing-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
      ( ε)
      ( δ)
      ( p)
      ( q)
  is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ
    ε δ p q (Vp , Npq) =
    is-enclosing-cauchy-filter-ℝ
      ( V)
      ( ε)
      ( δ)
      ( raise-real-ℚ l1 p)
      ( raise-real-ℚ l1 q)
      ( Vp)
      ( preserves-neighborhoods-map-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ l1)
        ( isometry-raise-real-ℚ l1)
        ( δ)
        ( p)
        ( q)
        ( Npq))

  is-local-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-local-neighborhood-subtype-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-local-cauchy-filter-ℚ-cauchy-filter-ℝ
    ( ε , δ , p , q) =
    ( is-bounded-cauchy-filter-ℚ-cauchy-filter-ℝ ε δ p q ,
      is-enclosing-cauchy-filter-ℚ-cauchy-filter-ℝ ε δ p q)

  is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ :
    is-cauchy-filter-Pseudometric-Space
      ( l2)
      ( pseudometric-space-ℚ)
      ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ)
  is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ =
    ( is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-saturated-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-local-cauchy-filter-ℚ-cauchy-filter-ℝ)

  cauchy-filter-ℚ-cauchy-filter-ℝ : cauchy-filter-ℚ l2
  cauchy-filter-ℚ-cauchy-filter-ℝ =
    ( neighborhood-subtype-cauchy-filter-ℚ-cauchy-filter-ℝ ,
      is-cauchy-filter-cauchy-filter-ℚ-cauchy-filter-ℝ)

  real-cauchy-filter-ℝ : ℝ l2
  real-cauchy-filter-ℝ = real-cauchy-filter-ℚ cauchy-filter-ℚ-cauchy-filter-ℝ
```

### The real number induced by a Cauchy filter of real numbers is in the filter

```agda
module _
  {l : Level} (V : cauchy-filter-ℝ l l)
  where

  is-in-filter-real-cauchy-filter-ℝ :
    (ε : ℚ⁺) → is-in-cauchy-filter-ℝ V ε (real-cauchy-filter-ℝ V)
  is-in-filter-real-cauchy-filter-ℝ ε =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-subtype-cauchy-filter-ℝ
            ( V)
            ( ε)
            ( real-cauchy-filter-ℝ V))
    in do
      (δ , δ+δ<ε) ← double-le-ℚ⁺ ε
      (q , Vq) ← is-proper-cauchy-filter-ℚ-cauchy-filter-ℝ V δ

      is-monotonic-cauchy-filter-ℝ
        ( V)
        ( real-cauchy-filter-ℝ V)
        ( δ +ℚ⁺ δ)
        ( ε)
        ( δ+δ<ε)
        ( is-enclosing-cauchy-filter-ℝ
          ( V)
          ( δ)
          ( δ)
          ( raise-real-ℚ l q)
          ( real-cauchy-filter-ℝ V)
          ( Vq)
          ( is-symmetric-neighborhood-ℝ
            ( δ)
            ( real-cauchy-filter-ℝ V)
            ( raise-real-ℚ l q)
            ( is-in-neighborhood-real-is-in-cauchy-filter-ℚ
              ( cauchy-filter-ℚ-cauchy-filter-ℝ V)
              ( δ)
              ( q)
              ( Vq))))
```

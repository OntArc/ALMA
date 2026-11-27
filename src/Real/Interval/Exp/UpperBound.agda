------------------------------------------------------------------------
-- Upper bounds for expq from uniform bounds on the partial sums
--
-- 由部分和的一致界推出 expq 的上界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.UpperBound where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (<⇒≤; <-≤-trans; ≤-<-trans; +-monoˡ-≤; +-assoc; +-comm; +-identityʳ
  ; +-inverseˡ; <-irrefl)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; subst; subst₂)

open import Real.CauchyToInterval using (M)
open import Real.IntervalEquiv using (l; u)
open import Real.Interval using (RealI; δ; δ-pos; embedℚ)
open import Real.Interval.ContinuityRecipBasic using (l-cauchy→realI)
open import Real.Interval.Exp.Core using (expPartial; expSeq; expq)
open import Real.Interval.LimitLaws using (add-right-<)
open import Real.Interval.Node using (u-dyadic)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Series.Bounds using (le-self-add)

------------------------------------------------------------------------
-- The lemma
--
-- 引理

expq-le-of-partials : (q : ℚ) (0≤q : 0ℚ ≤ q) (C : ℚ)
                    → ((n : ℕ) → expPartial q n ≤ C)
                    → expq q 0≤q ≤ℝ embedℚ C
expq-le-of-partials q 0≤q C bound = λ (k , h) →
  let
    cs = expSeq q 0≤q

    dk : ℚ
    dk = δ k

    ap : ℚ
    ap = expPartial q (M cs k)

    eR : u (embedℚ C) k ≡ δ k + C
    eR = u-dyadic C k

    eL : l (expq q 0≤q) k ≡ ap + neg (δ k)
    eL = l-cauchy→realI cs k

    h' : δ k + C < ap + neg (δ k)
    h' = subst₂ (λ x y → x < y) eR eL h

    ap≤C : ap ≤ C
    ap≤C = bound (M cs k)

    upper : ap + neg dk ≤ C + neg dk
    upper = +-monoˡ-≤ (neg dk) ap≤C

    moved : dk + C < C + neg dk
    moved = <-≤-trans h' upper

    stept : (dk + C) + dk < (C + neg dk) + dk
    stept = add-right-< {x = dk + C} {y = C + neg dk} {z = dk} moved

    cancel : (C + neg dk) + dk ≡ C
    cancel = trans (+-assoc C (neg dk) dk)
               (trans (cong (λ z → C + z) (+-inverseˡ dk)) (+-identityʳ C))

    below : (dk + C) + dk < C
    below = subst (λ z → (dk + C) + dk < z) cancel stept

    grow : dk + C ≤ (dk + C) + dk
    grow = le-self-add {p = dk + C} {q = dk} (<⇒≤ (δ-pos k))

    dk+C<C : dk + C < C
    dk+C<C = ≤-<-trans grow below

    small : C ≤ C + dk
    small = le-self-add {p = C} {q = dk} (<⇒≤ (δ-pos k))

    shifted : C ≤ dk + C
    shifted = subst (λ z → C ≤ z) (+-comm C dk) small

    bad : C < C
    bad = ≤-<-trans shifted dk+C<C
  in
    ⊥-elim (<-irrefl refl bad)

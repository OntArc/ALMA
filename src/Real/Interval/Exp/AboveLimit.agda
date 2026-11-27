------------------------------------------------------------------------
-- Points below the limit are eventually exceeded
--
-- 低于极限的点最终会被超过
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.AboveLimit where

open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_; _-_)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; +-identityˡ; +-identityʳ; +-inverseʳ
  ; +-inverseˡ; +-assoc; +-comm; +-mono-≤; ≤-<-trans; <-≤-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; subst; subst₂)

open import Real using (CauchySeq)
open import Real.CauchyToInterval using (M)
open import Real.Interval using (RealI; δ; δ-pos; embedℚ)
open import Real.IntervalEquiv using (l; u)
open import Real.Interval.ContinuityRecipBasic using (l-cauchy→realI)
open import Real.Interval.Exp.Core using (expPartial; expSeq; expq)
open import Real.Interval.LimitLaws using (add-right-<)
open import Real.Interval.Node using (u-dyadic)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Series.Bounds using (le-self-add)

------------------------------------------------------------------------
-- The lemma
--
-- 引理

expq-above : (q : ℚ) (0≤q : 0ℚ ≤ q) (p : ℚ)
           → embedℚ p <ℝ expq q 0≤q
           → Σ ℕ (λ n → p ≤ expPartial q n)
expq-above q 0≤q p (k , h) =
  let
    cs : CauchySeq
    cs = expSeq q 0≤q

    dk : ℚ
    dk = δ k

    ap : ℚ
    ap = expPartial q (M cs k)

    eR : u (embedℚ p) k ≡ dk + p
    eR = u-dyadic p k

    eL : l (expq q 0≤q) k ≡ ap + neg dk
    eL = l-cauchy→realI cs k

    h' : dk + p < ap + neg dk
    h' = subst₂ (λ x y → x < y) eR eL h

    d₀ : 0ℚ < dk
    d₀ = δ-pos k

    left₀ : p ≤ p + dk
    left₀ = le-self-add {p = p} {q = dk} (<⇒≤ d₀)

    left : p ≤ dk + p
    left = subst (λ z → p ≤ z) (+-comm p dk) left₀

    left₂ : dk + p ≤ (dk + p) + dk
    left₂ = le-self-add {p = dk + p} {q = dk} (<⇒≤ d₀)

    step : (dk + p) + dk < (ap + neg dk) + dk
    step = add-right-< {x = dk + p} {y = ap + neg dk} {z = dk} h'

    eA : (ap + neg dk) + dk ≡ ap
    eA = trans (+-assoc ap (neg dk) dk)
           (trans (cong (λ z → ap + z) (+-inverseˡ dk)) (+-identityʳ ap))

    lt : (dk + p) + dk < ap
    lt = subst (λ y → (dk + p) + dk < y) eA step

    p<ap : p < ap
    p<ap = ≤-<-trans left (≤-<-trans left₂ lt)
  in
    M cs k , <⇒≤ p<ap

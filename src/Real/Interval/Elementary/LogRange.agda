------------------------------------------------------------------------
-- The range of the rational exponential is the positive line
--
-- 有理指数的取值覆盖整条正半轴
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.LogRange where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_; 1/_; NonZero; Positive) renaming (-_ to neg)
open import Data.Rational.Base using (positive)
open import Data.Rational.Properties using
  (<⇒≤; <-cmp; <-trans; +-identityˡ; +-identityʳ; +-comm; +-monoˡ-<; +-monoʳ-<
  ; *-identityˡ; *-identityʳ; *-assoc; *-comm; *-inverseˡ; *-inverseʳ
  ; *-distribˡ-+; neg-antimono-<; pos⇒nonZero; positive⁻¹; 1/pos⇒pos)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; sym; trans; subst)

open import Base.RationalRing using (0<1; neg-0; neg-involutive)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono; 0<embedℚ)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Exp.Core using (expPartial; expq)
open import Real.Interval.Exp.Order using (expPartial-two)
open import Real.Interval.Exp.PartialLe using (expPartial-le-expq)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-nonNeg; expq-total-ge-one; expq-total-neg)
open import Real.Interval.Exp.Approx using (expq-pos)
open import Real.Interval.Exp.Dense using (lt-split)
open import Real.Interval.Kit using (neg-of-nonpos)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using (≈⇒≤ℝ; ≤ℝ-<trans; <-≤ℝ-trans)
open import Real.Interval.Rational using (÷-pos; *-<-mono-right)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipOrder using (recipℝ-antitone-of)
open import Real.Interval.RecipLaws using (embedℚ-recip)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤)

------------------------------------------------------------------------
-- Strict increment by one
--
-- 加一严格变大

succ-gt : (p : ℚ) → p < p + 1ℚ
succ-gt p = subst (λ z → z < p + 1ℚ) (+-identityʳ p) (+-monoʳ-< p 0<1)

------------------------------------------------------------------------
-- Every rational height is reached
--
-- 每个有有理高度都被达到

expq-unbounded : (B : ℚ) → Σ ℚ (λ q → embedℚ B <ℝ expq-total q)
expq-unbounded B =
  let
    order : (0ℚ < B) ⊎ (B ≤ 0ℚ)
    order = lt-split 0ℚ B (<-cmp 0ℚ B)

    pos : 0ℚ < B → Σ ℚ (λ q → embedℚ B <ℝ expq-total q)
    pos 0<B =
      let
        q : ℚ
        q = B + 1ℚ

        0<q : 0ℚ < q
        0<q = <-trans 0<1
                (subst (λ z → z < q) (+-identityˡ 1ℚ) (+-monoˡ-< 1ℚ 0<B))

        B<q+1 : B < q + 1ℚ
        B<q+1 = <-trans (succ-gt B) (succ-gt q)

        B<1q : B < 1ℚ + q
        B<1q = subst (λ z → B < z) (+-comm q 1ℚ) B<q+1

        eb<e1q : embedℚ B <ℝ embedℚ (1ℚ + q)
        eb<e1q = embedℚ-mono B (1ℚ + q) B<1q

        0≤q : 0ℚ ≤ q
        0≤q = <⇒≤ 0<q

        h₂ : embedℚ (1ℚ + q) ≤ℝ expq q 0≤q
        h₂ = subst (λ z → z ≤ℝ expq q 0≤q)
               (cong embedℚ (expPartial-two q))
               (expPartial-le-expq q 0≤q (suc (suc zero)))

        h₃ : expq q 0≤q ≤ℝ expq-total q
        h₃ = ≈⇒≤ℝ (≈ℝ-sym (expq-total-nonNeg q 0≤q))
      in
        q , <-≤ℝ-trans eb<e1q (≤ℝ-trans h₂ h₃)

    nonpos : B ≤ 0ℚ → Σ ℚ (λ q → embedℚ B <ℝ expq-total q)
    nonpos B≤0 =
      let
        h₁ : embedℚ B ≤ℝ 0ℝ
        h₁ = embedℚ-≤ B 0ℚ B≤0

        h₂ : 1ℝ ≤ℝ expq-total 1ℚ
        h₂ = expq-total-ge-one 1ℚ (<⇒≤ 0<1)
      in
        1ℚ , <-≤ℝ-trans (≤ℝ-<trans h₁ 0ℝ<ℝ1ℝ) h₂
  in
    [ pos , nonpos ]′ order

------------------------------------------------------------------------
-- Small values: the rational exponential drops below any positive bound
--
-- 取值趋零：有理指数能压到任意正界之下

-- With `N = 1/e` the value at `-N` is the reciprocal of `expq N`, which is
-- at least `1 + N`; the real reciprocal is antitone on positives, and on
-- the embed it agrees with the rational quotient, so the value is at most
-- `1/(1+N)`. The rational estimate `1/(1+N) < e` follows by multiplying
-- `1 < e + 1 = e * (1 + N)` with the positive quotient and cancelling.
--
-- 取 N = 1/e，则 -N 处取值是 expq N 的倒数，而 expq N 至少 1 + N；实数倒数
-- 在正数上反单调，且与嵌入处的有理商一致，于是该值不超过 1/(1+N)
-- 有理估计 1/(1+N) < e 由 1 < e + 1 = e * (1 + N) 两边乘正商并相消得到。
expq-small : (e : ℚ) → 0ℚ < e → Σ ℚ (λ q → expq-total q <ℝ embedℚ e)
expq-small e 0<e =
  let
    nz-e : NonZero e
    nz-e = pos⇒nonZero e {{positive 0<e}}

    N : ℚ
    N = 1/_ e {{nz-e}}

    0<N : 0ℚ < N
    0<N = subst (λ z → 0ℚ < z) (*-identityˡ N)
            (÷-pos 1ℚ e {{positive 0<e}} 0<1)

    0<1N : 0ℚ < 1ℚ + N
    0<1N = <-trans 0<1
             (subst (λ z → z < 1ℚ + N) (+-identityʳ 1ℚ) (+-monoʳ-< 1ℚ 0<N))

    nz-1N : NonZero (1ℚ + N)
    nz-1N = pos⇒nonZero (1ℚ + N) {{positive 0<1N}}

    lo : ℚ
    lo = 1/_ (1ℚ + N) {{nz-1N}}

    eN : e * N ≡ 1ℚ
    eN = *-inverseʳ e {{nz-e}}

    dist : e * (1ℚ + N) ≡ e + 1ℚ
    dist = trans (*-distribˡ-+ e 1ℚ N) (cong₂ _+_ (*-identityʳ e) eN)

    1<e+1 : 1ℚ < e + 1ℚ
    1<e+1 = subst (λ z → z < e + 1ℚ) (+-identityˡ 1ℚ) (+-monoˡ-< 1ℚ 0<e)

    step1 : 1ℚ < e * (1ℚ + N)
    step1 = subst (λ z → 1ℚ < z) (sym dist) 1<e+1

    0<lo : 0ℚ < lo
    0<lo = positive⁻¹ lo {{1/pos⇒pos (1ℚ + N) {{positive 0<1N}}}}

    mul : 1ℚ * lo < (e * (1ℚ + N)) * lo
    mul = *-<-mono-right 1ℚ (e * (1ℚ + N)) lo step1 0<lo

    1N-lo : (1ℚ + N) * lo ≡ 1ℚ
    1N-lo = trans (*-comm (1ℚ + N) lo) (*-inverseˡ (1ℚ + N) {{nz-1N}})

    rhs≡ : (e * (1ℚ + N)) * lo ≡ e
    rhs≡ = trans (*-assoc e (1ℚ + N) lo)
             (trans (cong (e *_) 1N-lo) (*-identityʳ e))

    lo<e : lo < e
    lo<e = subst (λ z → lo < z) rhs≡
             (subst (λ z → z < (e * (1ℚ + N)) * lo) (*-identityˡ lo) mul)

    q : ℚ
    q = neg N

    q<0 : q < 0ℚ
    q<0 = subst (λ z → neg N < z) neg-0 (neg-antimono-< 0<N)

    q≤0 : q ≤ 0ℚ
    q≤0 = <⇒≤ q<0

    pN : 0ℚ ≤ neg q
    pN = neg-of-nonpos {x = q} q≤0

    buff : 0ℝ <ℝ embedℚ (1ℚ + N)
    buff = 0<embedℚ (1ℚ + N) 0<1N

    pl : embedℚ (1ℚ + N) ≤ℝ expq (neg q) pN
    pl = subst (λ z → embedℚ z ≤ℝ expq (neg q) pN)
           (cong (λ z → 1ℚ + z) (neg-involutive N))
           (subst (λ z → z ≤ℝ expq (neg q) pN)
             (cong embedℚ (expPartial-two (neg q)))
             (expPartial-le-expq (neg q) pN (suc (suc zero))))

    a : expq-total q ≈ℝ recipℝ (expq (neg q) pN) (expq-pos (neg q) pN)
    a = expq-total-neg q q<0

    mono : recipℝ (expq (neg q) pN) (expq-pos (neg q) pN) ≤ℝ
           recipℝ (embedℚ (1ℚ + N)) buff
    mono = recipℝ-antitone-of (embedℚ (1ℚ + N)) (expq (neg q) pN)
             buff (expq-pos (neg q) pN) pl

    h4 : recipℝ (embedℚ (1ℚ + N)) buff ≈ℝ embedℚ lo
    h4 = ≈ℝ-sym (embedℚ-recip (1ℚ + N) {{nz-1N}} 0<1N)

    le : expq-total q ≤ℝ embedℚ lo
    le = ≤ℝ-trans (≈⇒≤ℝ a) (≤ℝ-trans mono (≈⇒≤ℝ h4))

    h5 : embedℚ lo <ℝ embedℚ e
    h5 = embedℚ-mono lo e lo<e
  in
    q , ≤ℝ-<trans le h5

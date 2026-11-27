------------------------------------------------------------------------
-- Windows around one
--
-- 一附近的窗口
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Dense where

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; -_; 1/_; NonZero; Positive)
open import Data.Rational.Base using (positive)
open import Data.Rational.Properties using
  (≤-refl; <⇒≤; <-cmp; <-trans; positive⁻¹; 1/pos⇒pos; pos⇒nonZero)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; subst)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono; 0<embedℚ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.OrderLe using (≈⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤)
open import Real.Interval.Rational using (recip-lt-of-lt)
open import Real.Interval.Kit using (recip-antitone)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using
  (recipℝ-pos; recipℝ-cong; recipℝ-invol; embedℚ-recip)
open import Real.Interval.RecipOrder using (recipℝ-strict-antitone-of)
open import Real.Interval.Exp.Approx using (expq-pos)
open import Real.Interval.Exp.Core using (expq)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-zero; expq-total-pos; expq-total-nonNeg
  ; expq-total-le-one; expq-total-neg-pos)
open import Real.Interval.Exp.Cross using (expq-cross-above)

------------------------------------------------------------------------
-- Deciding the two comparisons
--
-- 判定两种比较

-- `p ≤ q` versus `q < p`.
--
-- `p ≤ q` 与 `q < p` 二择一。
le-split : (p q : ℚ) → Tri (p < q) (p ≡ q) (q < p) → (p ≤ q) ⊎ (q < p)
le-split p q (tri< p<q _ _) = inj₁ (<⇒≤ p<q)
le-split p q (tri≈ _ p≡q _) = inj₁ (subst (λ z → p ≤ z) p≡q (≤-refl {p}))
le-split p q (tri> _ _ q<p) = inj₂ q<p

-- `p < q` versus `q ≤ p`.
--
-- `p < q` 与 `q ≤ p` 二择一。
lt-split : (p q : ℚ) → Tri (p < q) (p ≡ q) (q < p) → (p < q) ⊎ (q ≤ p)
lt-split p q (tri< p<q _ _) = inj₁ p<q
lt-split p q (tri≈ _ p≡q _) = inj₂ (subst (λ z → q ≤ z) (sym p≡q) (≤-refl {q}))
lt-split p q (tri> _ _ q<p) = inj₂ (<⇒≤ q<p)

------------------------------------------------------------------------
-- The crossing through one
--
-- 穿过一的跨越

-- Taking `q = 0` when the window straddles one: `exp 0 ≈ 1`, and the
-- strict monotonicity of the embedding supplies both sides.
--
-- 窗口跨一时取 `q = 0`：`exp 0 ≈ 1`，而 `r₁ < 1 < r₂`，两侧都由嵌入的
-- 严格单调性给出。
expq-cross-one : (r₁ r₂ : ℚ) (r₁<1 : r₁ < 1ℚ) (1<r₂ : 1ℚ < r₂)
               → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                          × (expq-total q <ℝ embedℚ r₂))
expq-cross-one r₁ r₂ r₁<1 1<r₂ =
  let
    lower-below : embedℚ r₁ <ℝ 1ℝ
    lower-below = embedℚ-mono r₁ 1ℚ r₁<1

    lower : embedℚ r₁ <ℝ expq-total 0ℚ
    lower = <-≤ℝ-trans lower-below (≈⇒≤ℝ (≈ℝ-sym expq-total-zero))

    upper-above : 1ℝ <ℝ embedℚ r₂
    upper-above = embedℚ-mono 1ℚ r₂ 1<r₂

    upper : expq-total 0ℚ <ℝ embedℚ r₂
    upper = ≤ℝ-<trans (≈⇒≤ℝ expq-total-zero) upper-above
  in
    0ℚ , (lower , upper)

------------------------------------------------------------------------
-- The sign of a point whose exponential exceeds one
--
-- 指数超过一的点的符号

-- Used by the reflection through one below: a point whose exponential
-- exceeds one cannot be non-positive, because below zero the total
-- exponential stays at most one (`expq-total-le-one`).
--
-- 供下面穿一的翻转使用：指数超过一的点不可能是非正的，因为零点以下全指数
-- 至多为一（`expq-total-le-one`）。
expq-point-pos : (q : ℚ) (1<x : 1ℝ <ℝ expq-total q) → 0ℚ < q
expq-point-pos q 1<x =
  let
    split : (0ℚ < q) ⊎ (q ≤ 0ℚ)
    split = lt-split 0ℚ q (<-cmp 0ℚ q)

    refute : q ≤ 0ℚ → 0ℚ < q
    refute q≤0 = ⊥-elim ((expq-total-le-one q q≤0) 1<x)

    pick : (0ℚ < q) ⊎ (q ≤ 0ℚ) → 0ℚ < q
    pick = [ (λ h → h) , refute ]
  in
    pick split

------------------------------------------------------------------------
-- The window below one
--
-- 一以下的窗口

-- A window with `r₂ ≤ 1` lies entirely below one, so no non-negative
-- power of e lands inside it. Reflect the window through the reciprocal
-- instead: `s₁ = 1/r₂ ≤ 1 ≤ s₂ = 1/r₁` puts the reflected window above
-- one, and `Exp/Cross` supplies `q'` with `exp q'` inside `(s₁, s₂)`
-- Reflecting back gives `exp (- q') = 1/exp q'` inside `(r₁, r₂)`, the
-- negative numerator being exactly the point where the total exponential
-- is a reciprocal (`expq-total-neg-pos`).
--
-- 当 `r₂ ≤ 1` 时窗口整个落在一以下，非负指数的 e 的幂不会落进去。改为把窗口
-- 经倒数翻转：`s₁ = 1/r₂ ≤ 1 ≤ s₂ = 1/r₁` 使翻转后的窗口位于一以上，由
-- `Exp/Cross` 给出 `q'` 使 `exp q'` 落在 `(s₁, s₂)` 内。再翻回来即
-- `exp (- q') = 1/exp q'` 落在 `(r₁, r₂)` 内；负分子正是全指数取倒数的点
-- （见 `expq-total-neg-pos`）。
expq-cross-below : (r₁ r₂ : ℚ) (0<r₁ : 0ℚ < r₁) (r₁<r₂ : r₁ < r₂)
                   (r₂≤1 : r₂ ≤ 1ℚ)
                 → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                            × (expq-total q <ℝ embedℚ r₂))
expq-cross-below r₁ r₂ 0<r₁ r₁<r₂ r₂≤1 =
  let
    0<r₂ : 0ℚ < r₂
    0<r₂ = <-trans 0<r₁ r₁<r₂

    nz-r₁ : NonZero r₁
    nz-r₁ = pos⇒nonZero r₁ {{positive 0<r₁}}

    nz-r₂ : NonZero r₂
    nz-r₂ = pos⇒nonZero r₂ {{positive 0<r₂}}

    -- The reflected window, above one.
    --
    -- 反射窗口，位于一之上。
    s₁ : ℚ
    s₁ = 1/_ r₂ {{nz-r₂}}

    s₂ : ℚ
    s₂ = 1/_ r₁ {{nz-r₁}}

    0<s₁ : 0ℚ < s₁
    0<s₁ = positive⁻¹ s₁ {{1/pos⇒pos r₂ {{positive 0<r₂}}}}

    0<s₂ : 0ℚ < s₂
    0<s₂ = positive⁻¹ s₂ {{1/pos⇒pos r₁ {{positive 0<r₁}}}}

    -- `1/r₂ ≤ 1 ≤ 1/r₁`, since the reciprocal reverses the comparison.
    --
    -- `1/r₂ ≤ 1 ≤ 1/r₁`，因为倒数反转比较。
    1≤s₁ : 1ℚ ≤ s₁
    1≤s₁ = recip-antitone {a = r₂} {b = 1ℚ} 0<r₂ r₂≤1

    s₁<s₂ : s₁ < s₂
    s₁<s₂ = recip-lt-of-lt r₁ r₂ {{positive 0<r₁}} {{positive 0<r₂}} r₁<r₂

    -- The crossing above one, inside the reflected window.
    --
    -- 一之上的交点，位于反射窗口之内。
    cross : Σ ℚ (λ q → (embedℚ s₁ <ℝ expq-total q)
                       × (expq-total q <ℝ embedℚ s₂))
    cross = expq-cross-above s₁ s₂ 1≤s₁ s₁<s₂

    q' : ℚ
    q' = proj₁ cross

    X : RealI
    X = expq-total q'

    below-q' : embedℚ s₁ <ℝ X
    below-q' = proj₁ (proj₂ cross)

    above-q' : X <ℝ embedℚ s₂
    above-q' = proj₂ (proj₂ cross)

    pX : 0ℝ <ℝ X
    pX = expq-total-pos q'

    ps₁ : 0ℝ <ℝ embedℚ s₁
    ps₁ = 0<embedℚ s₁ 0<s₁

    ps₂ : 0ℝ <ℝ embedℚ s₂
    ps₂ = 0<embedℚ s₂ 0<s₂

    p₁ : 0ℝ <ℝ embedℚ r₁
    p₁ = 0<embedℚ r₁ 0<r₁

    p₂ : 0ℝ <ℝ embedℚ r₂
    p₂ = 0<embedℚ r₂ 0<r₂

    1≤s₁ℝ : 1ℝ ≤ℝ embedℚ s₁
    1≤s₁ℝ = embedℚ-≤ 1ℚ s₁ 1≤s₁

    1<X : 1ℝ <ℝ X
    1<X = ≤ℝ-<trans 1≤s₁ℝ below-q'

    -- The numerator is positive, so the negative branch applies.
    --
    -- 分子为正，故适用负分支。
    0<q' : 0ℚ < q'
    0<q' = expq-point-pos q' 1<X

    q-eq : expq q' (<⇒≤ 0<q') ≈ℝ X
    q-eq = ≈ℝ-sym (expq-total-nonNeg q' (<⇒≤ 0<q'))

    inv-eq : recipℝ (expq q' (<⇒≤ 0<q')) (expq-pos q' (<⇒≤ 0<q'))
           ≈ℝ recipℝ X pX
    inv-eq = recipℝ-cong (expq q' (<⇒≤ 0<q')) X
                (expq-pos q' (<⇒≤ 0<q')) pX q-eq

    neg-eq : expq-total (- q') ≈ℝ recipℝ X pX
    neg-eq = ≈ℝ-trans (expq-total-neg-pos q' 0<q') inv-eq

    -- `1/s₁` is `1/(1/r₂)`, which is `r₂` again.
    --
    -- `1/s₁` 即 `1/(1/r₂)`，又回到 `r₂`。
    recip-s₁ : recipℝ (embedℚ s₁) ps₁
             ≈ℝ recipℝ (recipℝ (embedℚ r₂) p₂) (recipℝ-pos (embedℚ r₂) p₂)
    recip-s₁ = recipℝ-cong (embedℚ s₁) (recipℝ (embedℚ r₂) p₂)
                 ps₁ (recipℝ-pos (embedℚ r₂) p₂)
                 (embedℚ-recip r₂ ⦃ nz-r₂ ⦄ 0<r₂)

    back-s₁ : recipℝ (embedℚ s₁) ps₁ ≈ℝ embedℚ r₂
    back-s₁ = ≈ℝ-trans recip-s₁ (recipℝ-invol (embedℚ r₂) p₂)

    -- The reciprocal reverses the comparison, so `X > s₁` gives `1/X < 1/s₁`.
    --
    -- 倒数反转比较，故 `X > s₁` 给出 `1/X < 1/s₁`。
    upper-recip : recipℝ X pX <ℝ recipℝ (embedℚ s₁) ps₁
    upper-recip = recipℝ-strict-antitone-of (embedℚ s₁) X ps₁ pX below-q'

    upper-half : recipℝ X pX <ℝ embedℚ r₂
    upper-half = <-≤ℝ-trans upper-recip (≈⇒≤ℝ back-s₁)

    upper : expq-total (- q') <ℝ embedℚ r₂
    upper = ≤ℝ-<trans (≈⇒≤ℝ neg-eq) upper-half

    -- The same for the other end: `1/s₂` is `1/(1/r₁)`, which is `r₁` again.
    --
    -- 另一端同理：`1/s₂` 即 `1/(1/r₁)`，又回到 `r₁`。
    recip-s₂ : recipℝ (embedℚ s₂) ps₂
             ≈ℝ recipℝ (recipℝ (embedℚ r₁) p₁) (recipℝ-pos (embedℚ r₁) p₁)
    recip-s₂ = recipℝ-cong (embedℚ s₂) (recipℝ (embedℚ r₁) p₁)
                 ps₂ (recipℝ-pos (embedℚ r₁) p₁)
                 (embedℚ-recip r₁ ⦃ nz-r₁ ⦄ 0<r₁)

    back-s₂ : recipℝ (embedℚ s₂) ps₂ ≈ℝ embedℚ r₁
    back-s₂ = ≈ℝ-trans recip-s₂ (recipℝ-invol (embedℚ r₁) p₁)

    lower-recip : recipℝ (embedℚ s₂) ps₂ <ℝ recipℝ X pX
    lower-recip = recipℝ-strict-antitone-of X (embedℚ s₂) pX ps₂ above-q'

    lower-half : embedℚ r₁ <ℝ recipℝ X pX
    lower-half = ≤ℝ-<trans (≈⇒≤ℝ (≈ℝ-sym back-s₂)) lower-recip

    lower : embedℚ r₁ <ℝ expq-total (- q')
    lower = <-≤ℝ-trans lower-half (≈⇒≤ℝ (≈ℝ-sym neg-eq))
  in
    (- q') , (lower , upper)

------------------------------------------------------------------------
-- The window witness, all three ranges
--
-- 三段合一的窗口见证

-- A window opening below one is either straddling or entirely below, so
-- the second split decides between `expq-cross-one` and
-- `expq-cross-below`. A window opening at or above one is the `Exp/Cross`
-- range. This closes the case analysis that `expq-dense` needs.
--
-- 下界在一以下的窗口或跨一、或整个在一以下，故第二次拆分在
-- `expq-cross-one` 与 `expq-cross-below` 之间取舍；下界不低于一的窗口就是
-- `Exp/Cross` 的那一段。至此 `expq-dense` 所需的情形分析闭合。
expq-cross-under-one : (r₁ r₂ : ℚ) (0<r₁ : 0ℚ < r₁) (r₁<1 : r₁ < 1ℚ)
                       (r₁<r₂ : r₁ < r₂)
                       (split : (1ℚ < r₂) ⊎ (r₂ ≤ 1ℚ))
                     → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                                × (expq-total q <ℝ embedℚ r₂))
expq-cross-under-one r₁ r₂ 0<r₁ r₁<1 r₁<r₂ split =
  let
    window : Set
    window = Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                          × (expq-total q <ℝ embedℚ r₂))

    pick : (1ℚ < r₂) ⊎ (r₂ ≤ 1ℚ) → window
    pick = [ (λ 1<r₂ → expq-cross-one r₁ r₂ r₁<1 1<r₂)
           , (λ r₂≤1 → expq-cross-below r₁ r₂ 0<r₁ r₁<r₂ r₂≤1) ]
  in
    pick split

-- A rational strictly between two rationals is the exponential of a
-- rational: the three ranges above cover every window.
--
-- 夹在两有理数之间的有理数必是某有理数的指数：上面三段覆盖了所有窗口。
expq-dense : (r₁ r₂ : ℚ) (0<r₁ : 0ℚ < r₁) (r₁<r₂ : r₁ < r₂)
           → Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                      × (expq-total q <ℝ embedℚ r₂))
expq-dense r₁ r₂ 0<r₁ r₁<r₂ =
  let
    window : Set
    window = Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                          × (expq-total q <ℝ embedℚ r₂))

    above : 1ℚ ≤ r₁ → window
    above 1≤r₁ = expq-cross-above r₁ r₂ 1≤r₁ r₁<r₂

    below : r₁ < 1ℚ → window
    below r₁<1 = expq-cross-under-one r₁ r₂ 0<r₁ r₁<1 r₁<r₂
                   (lt-split 1ℚ r₂ (<-cmp 1ℚ r₂))

    pick : (1ℚ ≤ r₁) ⊎ (r₁ < 1ℚ) → window
    pick = [ above , below ]
  in
    pick (le-split 1ℚ r₁ (<-cmp 1ℚ r₁))

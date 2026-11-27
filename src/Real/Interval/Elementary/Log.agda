------------------------------------------------------------------------
-- The inverse laws of the logarithm and the exponential
--
-- 对数与指数的互逆律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.Log where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_)
open import Data.Rational.Properties using (<⇒≤; ≤-<-trans; <-cmp; <-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Base.RationalRing using (0<1)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Elementary.ExpLaws using (expℝ-cong; expℝ-zero)
open import Real.Interval.Elementary.Exp using
  (Pℝ; Pℝ-member; Pℝ-zero; Pℝ-isUpper; located; expℝ; expℝ-le-of-partials)
open import Real.Interval.Elementary.Continuous using (expPartialℝ-below-rat)
open import Real.Interval.Elementary.LogAdjunction using
  (expq-le-of-lt-log; log-le-rat-of-lt-expq; rat-lt-log-of-expq-lt)
open import Real.Interval.Elementary.ExpRat using (expPartialℝ-at-rat)
open import Real.Interval.Exp.Core using (expPartial; expq)
open import Real.Interval.Exp.PartialLe using (expPartial-le-expq)
open import Real.Interval.Exp.Dense using (expq-dense; lt-split)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-nonNeg; expq-total-le-one)
open import Real.Interval.Exp.Series using (expPartialℝ; expPartialℝ-mono)
open import Real.Interval.Exp.AboveLimit using (expq-above)
open import Real.Interval.Log.Full using (logℝ-total; log-total-member)
open import Real.Interval.Log.Order using
  (log-total-nonNeg; log-total-pos; log-total-cong; log-total-one)
open import Real.Interval.Order using (_<ℝ_) renaming (<-trans to <-transR)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (≈⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans; <⇒≤ℝ; ≤ℝ-antisym; ≤ℝ-refl)
open import Real.Interval.OrderComplete.Limit using (sup-≤-of-limit)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤; embedℚ-reflect)

------------------------------------------------------------------------
-- The rational window for the lower half
--
-- 下半所用的有理窗口

-- Given `p` and `1 < y`, produce `r₁ < r₂` with `p < r₁`, `1 < r₁` and
-- `embed r₂ < y`. When `p` already exceeds `1`, the window is opened above
-- `p`; otherwise it is cut above `1` directly and `p` follows from
-- `p ≤ 1 < r₁`. Density supplies both ends in turn.
--
-- 给定 `p` 与 `1 < y`，产出 `r₁ < r₂`，使 `p < r₁`、`1 < r₁` 且
-- `embed r₂ < y`。`p` 已超过 `1` 时窗口开在 `p` 之上；否则直接从 `1` 之上
-- 切出，`p` 由 `p ≤ 1 < r₁` 得。两端都靠稠密性逐个给出。
exp-log-window : (y : RealI) (1<y : 1ℝ <ℝ y) (p : ℚ)
                 (p<y : embedℚ p <ℝ y)
               → (1ℚ < p) ⊎ (p ≤ 1ℚ)
               → Σ ℚ (λ r₁ → Σ ℚ (λ r₂ → (p < r₁) × (1ℚ < r₁)
                                          × (r₁ < r₂) × (embedℚ r₂ <ℝ y)))
exp-log-window y 1<y p p<y (inj₁ 1<p) =
  let
    w₁ : Σ ℚ (λ r₁ → (embedℚ p <ℝ embedℚ r₁) × (embedℚ r₁ <ℝ y))
    w₁ = dense p<y

    r₁ : ℚ
    r₁ = proj₁ w₁

    ep<er₁ : embedℚ p <ℝ embedℚ r₁
    ep<er₁ = proj₁ (proj₂ w₁)

    er₁<y : embedℚ r₁ <ℝ y
    er₁<y = proj₂ (proj₂ w₁)

    p<r₁ : p < r₁
    p<r₁ = embedℚ-reflect p r₁ ep<er₁

    1<r₁ : 1ℚ < r₁
    1<r₁ = <-trans 1<p p<r₁

    w₂ : Σ ℚ (λ r₂ → (embedℚ r₁ <ℝ embedℚ r₂) × (embedℚ r₂ <ℝ y))
    w₂ = dense er₁<y

    r₂ : ℚ
    r₂ = proj₁ w₂

    er₁<er₂ : embedℚ r₁ <ℝ embedℚ r₂
    er₁<er₂ = proj₁ (proj₂ w₂)

    er₂<y : embedℚ r₂ <ℝ y
    er₂<y = proj₂ (proj₂ w₂)

    r₁<r₂ : r₁ < r₂
    r₁<r₂ = embedℚ-reflect r₁ r₂ er₁<er₂
  in
    (r₁ , (r₂ , (p<r₁ , (1<r₁ , (r₁<r₂ , er₂<y)))))
exp-log-window y 1<y p p<y (inj₂ p≤1) =
  let
    w₁ : Σ ℚ (λ r₁ → (1ℝ <ℝ embedℚ r₁) × (embedℚ r₁ <ℝ y))
    w₁ = dense 1<y

    r₁ : ℚ
    r₁ = proj₁ w₁

    e1<er₁ : 1ℝ <ℝ embedℚ r₁
    e1<er₁ = proj₁ (proj₂ w₁)

    er₁<y : embedℚ r₁ <ℝ y
    er₁<y = proj₂ (proj₂ w₁)

    1<r₁ : 1ℚ < r₁
    1<r₁ = embedℚ-reflect 1ℚ r₁ e1<er₁

    p<r₁ : p < r₁
    p<r₁ = ≤-<-trans p≤1 1<r₁

    w₂ : Σ ℚ (λ r₂ → (embedℚ r₁ <ℝ embedℚ r₂) × (embedℚ r₂ <ℝ y))
    w₂ = dense er₁<y

    r₂ : ℚ
    r₂ = proj₁ w₂

    er₁<er₂ : embedℚ r₁ <ℝ embedℚ r₂
    er₁<er₂ = proj₁ (proj₂ w₂)

    er₂<y : embedℚ r₂ <ℝ y
    er₂<y = proj₂ (proj₂ w₂)

    r₁<r₂ : r₁ < r₂
    r₁<r₂ = embedℚ-reflect r₁ r₂ er₁<er₂
  in
    (r₁ , (r₂ , (p<r₁ , (1<r₁ , (r₁<r₂ , er₂<y)))))

-- Everything except the placement of the window is carried out here: the
-- exponential at `q₀` is positive and below `y`, so `q₀` is a member of
-- the logarithm and its partial sums are dominated by those at `log y`;
-- and the exponential exceeds `r₁`, which exceeds `1`, so `q₀` is positive
-- and its partial sums eventually pass `p`. The caller only has to
-- produce the window with `p < r₁ < r₂ < y` and `1 < r₁`.
--
-- 由单个有理窗口给出割在该点之上的成员
-- 除窗口的摆放之外，其余都在这里完成：`q₀` 处的指数为正且低于 `y`，故 `q₀`
-- 是对数的成员，其部分和被 `log y` 处的部分和支配；又该指数超过 `r₁` 而
-- `r₁` 超过 `1`，故 `q₀` 为正，其部分和最终越过 `p`。调用方只需造出满足
-- `p < r₁ < r₂ < y` 与 `1 < r₁` 的窗口。
expℝ-log-member : (y : RealI) (0<y : 0ℝ <ℝ y) (1<y : 1ℝ <ℝ y)
                  (p : ℚ) (z : RealI) (z<p : z <ℝ embedℚ p)
                  (r₁ r₂ : ℚ)
                  (p<r₁ : p < r₁) (1<r₁ : 1ℚ < r₁) (r₁<r₂ : r₁ < r₂)
                  (er₂<y : embedℚ r₂ <ℝ y)
                → Σ RealI (λ z' →
                    Pℝ (logℝ-total y 0<y)
                       (log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)) z'
                    × (z <ℝ z'))
expℝ-log-member y 0<y 1<y p z z<p r₁ r₂ p<r₁ 1<r₁ r₁<r₂ er₂<y =
  let
    x : RealI
    x = logℝ-total y 0<y

    0≤x : 0ℝ ≤ℝ x
    0≤x = log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)

    0<r₁ : 0ℚ < r₁
    0<r₁ = <-trans 0<1 1<r₁

    winq : Σ ℚ (λ q → (embedℚ r₁ <ℝ expq-total q)
                   × (expq-total q <ℝ embedℚ r₂))
    winq = expq-dense r₁ r₂ 0<r₁ r₁<r₂

    q₀ : ℚ
    q₀ = proj₁ winq

    er₁<eq₀ : embedℚ r₁ <ℝ expq-total q₀
    er₁<eq₀ = proj₁ (proj₂ winq)

    eq₀<er₂ : expq-total q₀ <ℝ embedℚ r₂
    eq₀<er₂ = proj₂ (proj₂ winq)

    1≤e : 1ℝ ≤ℝ embedℚ r₁
    1≤e = <⇒≤ℝ (embedℚ-mono 1ℚ r₁ 1<r₁)

    -- A non-positive point would make the exponential at most one, while
    -- `r₁` already exceeds one.
    --
    -- 非正的点指数至多为一，而 `r₁` 已超过一。
    contra : q₀ ≤ 0ℚ → ⊥
    contra q₀≤0 =
      1≤e (<-≤ℝ-trans er₁<eq₀ (expq-total-le-one q₀ q₀≤0))

    pos : (0ℚ < q₀) ⊎ (q₀ ≤ 0ℚ) → 0ℚ < q₀
    pos = λ { (inj₁ 0<q) → 0<q
            ; (inj₂ q≤0) → ⊥-elim (contra q≤0) }

    0<q₀ : 0ℚ < q₀
    0<q₀ = pos (lt-split 0ℚ q₀ (<-cmp 0ℚ q₀))

    0≤q₀ : 0ℚ ≤ q₀
    0≤q₀ = <⇒≤ 0<q₀

    q₀<y : expq-total q₀ <ℝ y
    q₀<y = <-transR eq₀<er₂ er₂<y

    eq₀≤x : embedℚ q₀ ≤ℝ x
    eq₀≤x = log-total-member y 0<y q₀ q₀<y

    ep≤er₁ : embedℚ p ≤ℝ embedℚ r₁
    ep≤er₁ = embedℚ-≤ p r₁ (<⇒≤ p<r₁)

    er₁<eqq : embedℚ r₁ <ℝ expq q₀ 0≤q₀
    er₁<eqq = <-≤ℝ-trans er₁<eq₀
      (≈⇒≤ℝ (expq-total-nonNeg q₀ 0≤q₀))

    ep<eqq : embedℚ p <ℝ expq q₀ 0≤q₀
    ep<eqq = ≤ℝ-<trans ep≤er₁ er₁<eqq

    w : Σ ℕ (λ n → p ≤ expPartial q₀ n)
    w = expq-above q₀ 0≤q₀ p ep<eqq

    n : ℕ
    n = proj₁ w

    p≤part : p ≤ expPartial q₀ n
    p≤part = proj₂ w

    0≤eq₀ : 0ℝ ≤ℝ embedℚ q₀
    0≤eq₀ = embedℚ-≤ 0ℚ q₀ 0≤q₀

    part≤x : embedℚ (expPartial q₀ n) ≤ℝ expPartialℝ x n
    part≤x = ≤ℝ-trans
      (≈⇒≤ℝ (≈ℝ-sym (expPartialℝ-at-rat q₀ 0≤q₀ n)))
      (expPartialℝ-mono (embedℚ q₀) x 0≤eq₀ eq₀≤x n)

    mem : Pℝ x 0≤x (embedℚ (expPartial q₀ n))
    mem = Pℝ-member x 0≤x (expPartial q₀ n) (n , part≤x)

    z<part : z <ℝ embedℚ (expPartial q₀ n)
    z<part = <-≤ℝ-trans z<p (embedℚ-≤ p (expPartial q₀ n) p≤part)
  in
    embedℚ (expPartial q₀ n) , (mem , z<part)

------------------------------------------------------------------------
-- The cut is above `y`
--
-- 割在 y 之上

-- The branch `y ≈ 1` is not a value-level gap and is not derived here:
-- `log 1 ≈ 0` and `exp 0 ≈ 1` settle it below, through congruence.
--
-- `y ≈ 1` 一支不是取值层面的缺口，也不在此处推导：它由 `log 1 ≈ 0` 与
-- `exp 0 ≈ 1` 在下文经同余直接收拾。
y-le-expℝ-log : (y : RealI) (0<y : 0ℝ <ℝ y) (1<y : 1ℝ <ℝ y)
              → y ≤ℝ expℝ (logℝ-total y 0<y)
                              (log-total-nonNeg y 0<y (<⇒≤ℝ 1<y))
y-le-expℝ-log y 0<y 1<y E<y =
  let
    x : RealI
    x = logℝ-total y 0<y

    0≤x : 0ℝ ≤ℝ x
    0≤x = log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)

    E : RealI
    E = expℝ x 0≤x

    win : Σ ℚ (λ q → (E <ℝ embedℚ q) × (embedℚ q <ℝ y))
    win = dense E<y

    q : ℚ
    q = proj₁ win

    E<q : E <ℝ embedℚ q
    E<q = proj₁ (proj₂ win)

    q<y : embedℚ q <ℝ y
    q<y = proj₂ (proj₂ win)

    hyp : (z : RealI) → z <ℝ embedℚ q
        → Σ RealI (λ z' → Pℝ x 0≤x z' × (z <ℝ z'))
    hyp z z<q =
      let
        wz : Σ ℚ (λ p → (z <ℝ embedℚ p) × (embedℚ p <ℝ embedℚ q))
        wz = dense z<q

        p : ℚ
        p = proj₁ wz

        z<p : z <ℝ embedℚ p
        z<p = proj₁ (proj₂ wz)

        ep<eq : embedℚ p <ℝ embedℚ q
        ep<eq = proj₂ (proj₂ wz)

        p<y : embedℚ p <ℝ y
        p<y = <-transR ep<eq q<y

        winr : Σ ℚ (λ r₁ → Σ ℚ (λ r₂ → (p < r₁) × (1ℚ < r₁)
                                        × (r₁ < r₂) × (embedℚ r₂ <ℝ y)))
        winr = exp-log-window y 1<y p p<y (lt-split 1ℚ p (<-cmp 1ℚ p))

        r₁ : ℚ
        r₁ = proj₁ winr

        wr : Σ ℚ (λ r₂ → (p < r₁) × (1ℚ < r₁) × (r₁ < r₂) × (embedℚ r₂ <ℝ y))
        wr = proj₂ winr

        r₂ : ℚ
        r₂ = proj₁ wr

        wv : (p < r₁) × (1ℚ < r₁) × (r₁ < r₂) × (embedℚ r₂ <ℝ y)
        wv = proj₂ wr

        p<r₁ : p < r₁
        p<r₁ = proj₁ wv

        wv₂ : (1ℚ < r₁) × (r₁ < r₂) × (embedℚ r₂ <ℝ y)
        wv₂ = proj₂ wv

        1<r₁ : 1ℚ < r₁
        1<r₁ = proj₁ wv₂

        wv₃ : (r₁ < r₂) × (embedℚ r₂ <ℝ y)
        wv₃ = proj₂ wv₂

        r₁<r₂ : r₁ < r₂
        r₁<r₂ = proj₁ wv₃

        er₂<y : embedℚ r₂ <ℝ y
        er₂<y = proj₂ wv₃
      in
        expℝ-log-member y 0<y 1<y p z z<p r₁ r₂ p<r₁ 1<r₁ r₁<r₂ er₂<y

    q≤E : embedℚ q ≤ℝ E
    q≤E = sup-≤-of-limit {P = Pℝ x 0≤x} (located x 0≤x) (Pℝ-zero x 0≤x)
             (Pℝ-isUpper x 0≤x) q hyp
  in
    q≤E E<q

------------------------------------------------------------------------
-- The cut is below `y`
--
-- 割在 y 之下

-- The upper half reduces, through `expℝ-le-of-partials`, to `y` bounding
-- every partial sum at `log y`. Suppose a partial sum crept above `y`
-- Density puts a rational `r` strictly between them; continuity at `log y`
-- (`expPartialℝ-below-rat`) then pulls out a non-negative rational point
-- `q` below `log y` whose partial sum still exceeds `r`. At a rational
-- point the partial sum is an embedded rational partial sum, which is at
-- most the total exponential there; and `q < log y` makes that total
-- exponential at most `y` by the adjunction `expq-le-of-lt-log`. So `r` is
-- at most `y` while `y` is strictly below `r` — which is the refutation.
--
-- 上半经 `expℝ-le-of-partials` 化为"`y` 界住 `log y` 处的每个部分和"。反设
-- 某个部分和窜到 `y` 之上：稠密性在两者之间放一个有理点 `r`，`log y` 处的
-- 连续性（`expPartialℝ-below-rat`）随即逼出 `log y` 下方的一个非负有有理点
-- `q`，其部分和仍超过 `r`。在有理点处部分和就是嵌入的有理部分和，它不超过
-- 该点的总指数；而 `q < log y` 由伴随律 `expq-le-of-lt-log` 使该总指数不超过
-- `y`。于是 `r` 不超过 `y`，可 `y` 又严格低于 `r`——这正是反驳。
expℝ-log-le : (y : RealI) (0<y : 0ℝ <ℝ y) (1<y : 1ℝ <ℝ y)
            → expℝ (logℝ-total y 0<y)
                    (log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)) ≤ℝ y
expℝ-log-le y 0<y 1<y =
  let
    x : RealI
    x = logℝ-total y 0<y

    0≤x : 0ℝ ≤ℝ x
    0≤x = log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)

    0<x : 0ℝ <ℝ x
    0<x = log-total-pos y 0<y 1<y

    part≤y : (n : ℕ) → expPartialℝ x n ≤ℝ y
    part≤y n y<P =
      let
        win : Σ ℚ (λ r → (y <ℝ embedℚ r) × (embedℚ r <ℝ expPartialℝ x n))
        win = dense y<P

        r : ℚ
        r = proj₁ win

        y<er : y <ℝ embedℚ r
        y<er = proj₁ (proj₂ win)

        er<P : embedℚ r <ℝ expPartialℝ x n
        er<P = proj₂ (proj₂ win)

        blw : Σ ℚ (λ q → (0ℚ ≤ q) × (embedℚ q <ℝ x) ×
                     (embedℚ r <ℝ expPartialℝ (embedℚ q) n))
        blw = expPartialℝ-below-rat x 0<x n r er<P

        q : ℚ
        q = proj₁ blw

        0≤q : 0ℚ ≤ q
        0≤q = proj₁ (proj₂ blw)

        eq<x : embedℚ q <ℝ x
        eq<x = proj₁ (proj₂ (proj₂ blw))

        er<partq : embedℚ r <ℝ expPartialℝ (embedℚ q) n
        er<partq = proj₂ (proj₂ (proj₂ blw))

        q<log : embedℚ q <ℝ logℝ-total y 0<y
        q<log = eq<x

        er≤partq : embedℚ r ≤ℝ expPartialℝ (embedℚ q) n
        er≤partq = <⇒≤ℝ er<partq

        partq≈ : expPartialℝ (embedℚ q) n ≈ℝ embedℚ (expPartial q n)
        partq≈ = expPartialℝ-at-rat q 0≤q n

        partq≤rat : expPartialℝ (embedℚ q) n ≤ℝ embedℚ (expPartial q n)
        partq≤rat = ≈⇒≤ℝ partq≈

        rat≤expq : embedℚ (expPartial q n) ≤ℝ expq q 0≤q
        rat≤expq = expPartial-le-expq q 0≤q n

        expq≈ : expq q 0≤q ≈ℝ expq-total q
        expq≈ = ≈ℝ-sym (expq-total-nonNeg q 0≤q)

        expq≤total : expq q 0≤q ≤ℝ expq-total q
        expq≤total = ≈⇒≤ℝ expq≈

        total≤y : expq-total q ≤ℝ y
        total≤y = expq-le-of-lt-log y 0<y q q<log

        er≤y : embedℚ r ≤ℝ y
        er≤y = ≤ℝ-trans er≤partq
                 (≤ℝ-trans partq≤rat
                   (≤ℝ-trans rat≤expq
                     (≤ℝ-trans expq≤total total≤y)))
      in
        er≤y y<er
  in
    expℝ-le-of-partials x 0≤x y part≤y

------------------------------------------------------------------------
-- The round trip
--
-- 往返等式

-- The two halves pin `exp (log y)` between the same pair, so
-- antisymmetry turns them into an equality.
--
-- 两个方向把 `exp (log y)` 夹在同一对端点之间，反对称性把它们合成等式。
exp-log-roundtrip : (y : RealI) (0<y : 0ℝ <ℝ y) (1<y : 1ℝ <ℝ y)
                  → expℝ (logℝ-total y 0<y)
                          (log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)) ≈ℝ y
exp-log-roundtrip y 0<y 1<y =
  ≤ℝ-antisym (expℝ-log-le y 0<y 1<y) (y-le-expℝ-log y 0<y 1<y)

------------------------------------------------------------------------
-- The boundary `y ≈ 1`
--
-- 边界 `y ≈ 1`

-- At one the logarithm is zero and the exponential at zero is one, so the
-- round trip is not a value estimate at all: it is the congruence of the
-- exponential in its argument, run from `log y` to `0` and back to `1`.
--
-- 在一处对数为零、零处指数为一，故往返等式根本不是取值估计：它是指数在
-- 自变量上的同余，从 `log y` 走到 `0` 再走回 `1`。
exp-log-roundtrip-at-one : (y : RealI) (0<y : 0ℝ <ℝ y) (y≈1 : y ≈ℝ 1ℝ)
                         → expℝ (logℝ-total y 0<y)
                                 (log-total-nonNeg y 0<y (≈⇒≤ℝ (≈ℝ-sym y≈1)))
                           ≈ℝ y
exp-log-roundtrip-at-one y 0<y y≈1 =
  let
    x : RealI
    x = logℝ-total y 0<y

    0≤x : 0ℝ ≤ℝ x
    0≤x = log-total-nonNeg y 0<y (≈⇒≤ℝ (≈ℝ-sym y≈1))

    x≈0 : x ≈ℝ 0ℝ
    x≈0 = ≈ℝ-trans (log-total-cong y 1ℝ 0<y 0ℝ<ℝ1ℝ y≈1) log-total-one

    E≈1 : expℝ x 0≤x ≈ℝ 1ℝ
    E≈1 = ≈ℝ-trans (expℝ-cong x 0ℝ 0≤x (≤ℝ-refl {0ℝ}) x≈0) expℝ-zero
  in
    ≈ℝ-trans E≈1 (≈ℝ-sym y≈1)

------------------------------------------------------------------------
-- The logarithm is injective
--
-- 对数的单射性

-- Congruence carries `log y ≈ log z` to `exp (log y) ≈ exp (log z)`, and
-- the two round trips carry it back to `y ≈ z`. Together with
-- `log-total-cong` this makes the logarithm a bijection on `≈`: a
-- comparison at the level of the logarithms is the same comparison at the
-- level of the numbers.
--
-- 同余把 `log y ≈ log z` 推到 `exp (log y) ≈ exp (log z)`，两个往返等式再把
-- 它送回 `y ≈ z`。与 `log-total-cong` 合起来，对数在 `≈` 层面是双射：对数
-- 层面的比较与数本身的比较是同一个比较。
log-total-injective : (y z : RealI) (0<y : 0ℝ <ℝ y) (0<z : 0ℝ <ℝ z)
                      (1<y : 1ℝ <ℝ y) (1<z : 1ℝ <ℝ z)
                    → logℝ-total y 0<y ≈ℝ logℝ-total z 0<z → y ≈ℝ z
log-total-injective y z 0<y 0<z 1<y 1<z h =
  let
    x : RealI
    x = logℝ-total y 0<y

    x' : RealI
    x' = logℝ-total z 0<z

    0≤x : 0ℝ ≤ℝ x
    0≤x = log-total-nonNeg y 0<y (<⇒≤ℝ 1<y)

    0≤x' : 0ℝ ≤ℝ x'
    0≤x' = log-total-nonNeg z 0<z (<⇒≤ℝ 1<z)

    E≈ : expℝ x 0≤x ≈ℝ expℝ x' 0≤x'
    E≈ = expℝ-cong x x' 0≤x 0≤x' h

    y≈E : y ≈ℝ expℝ x 0≤x
    y≈E = ≈ℝ-sym (exp-log-roundtrip y 0<y 1<y)

    E'≈z : expℝ x' 0≤x' ≈ℝ z
    E'≈z = exp-log-roundtrip z 0<z 1<z
  in
    ≈ℝ-trans y≈E (≈ℝ-trans E≈ E'≈z)

------------------------------------------------------------------------
-- The logarithm is strictly monotone
--
-- 对数严格单调

-- `y < z` forces `log y < log z`. The strict comparison cannot come from
-- the exponentials alone — every comparison in the adjunction is
-- non-strict — so it is read off a rational window instead. Density first
-- puts `p` above `y` with `embed p < z`, then `r` between `embed p` and `z`;
-- `expq-dense` produces a rational `q` whose exponential lies strictly
-- between `embed p` and `embed r`. Then `y < expq q` puts `log y ≤ embed q`
-- (`log-le-rat-of-lt-expq`), while `expq q < z` puts `embed q < log z`
-- (`rat-lt-log-of-expq-lt`); the two compose through `≤ℝ-<trans`.
--
-- `y < z` 迫使 `log y < log z`。严格比较无法只从指数得到——伴随关系里的
-- 每个比较都是非严格的——于是改从一个有理窗口读出。稠密性先把 `p` 放在 `y`
-- 之上且 `embed p < z`，再把 `r` 放在 `embed p` 与 `z` 之间；`expq-dense`
-- 产出有理点 `q`，其指数严格落在 `embed p` 与 `embed r` 之间。于是
-- `y < expq q` 给出 `log y ≤ embed q`（`log-le-rat-of-lt-expq`），而
-- `expq q < z` 给出 `embed q < log z`（`rat-lt-log-of-expq-lt`）；两者经
-- `≤ℝ-<trans` 接上。
log-total-strict-mono : (y z : RealI) (0<y : 0ℝ <ℝ y) (0<z : 0ℝ <ℝ z)
                      → y <ℝ z
                      → logℝ-total y 0<y <ℝ logℝ-total z 0<z
log-total-strict-mono y z 0<y 0<z y<z =
  let
    w₁ : Σ ℚ (λ p → (y <ℝ embedℚ p) × (embedℚ p <ℝ z))
    w₁ = dense y<z

    p : ℚ
    p = proj₁ w₁

    y<p : y <ℝ embedℚ p
    y<p = proj₁ (proj₂ w₁)

    p<z : embedℚ p <ℝ z
    p<z = proj₂ (proj₂ w₁)

    w₂ : Σ ℚ (λ r → (embedℚ p <ℝ embedℚ r) × (embedℚ r <ℝ z))
    w₂ = dense p<z

    r : ℚ
    r = proj₁ w₂

    p<rE : embedℚ p <ℝ embedℚ r
    p<rE = proj₁ (proj₂ w₂)

    r<z : embedℚ r <ℝ z
    r<z = proj₂ (proj₂ w₂)

    0<p : 0ℚ < p
    0<p = embedℚ-reflect 0ℚ p (<-transR 0<y y<p)

    p<r : p < r
    p<r = embedℚ-reflect p r p<rE

    w₃ : Σ ℚ (λ q → (embedℚ p <ℝ expq-total q)
                     × (expq-total q <ℝ embedℚ r))
    w₃ = expq-dense p r 0<p p<r

    q : ℚ
    q = proj₁ w₃

    p<eq : embedℚ p <ℝ expq-total q
    p<eq = proj₁ (proj₂ w₃)

    eq<rE : expq-total q <ℝ embedℚ r
    eq<rE = proj₂ (proj₂ w₃)

    y<eq : y <ℝ expq-total q
    y<eq = <-transR y<p p<eq

    eq<z : expq-total q <ℝ z
    eq<z = <-transR eq<rE r<z

    y≤q : logℝ-total y 0<y ≤ℝ embedℚ q
    y≤q = log-le-rat-of-lt-expq y 0<y q y<eq

    q<log : embedℚ q <ℝ logℝ-total z 0<z
    q<log = rat-lt-log-of-expq-lt z 0<z q eq<z
  in
    ≤ℝ-<trans y≤q q<log

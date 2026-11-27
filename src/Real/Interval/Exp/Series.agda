------------------------------------------------------------------------
-- The exponential series over the reals
--
-- 实数上的指数级数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Series where

open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m+[n∸m]≡n)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _*_; _÷_; 1/_)
open import Data.Rational.Properties using (≤⇒≯)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Real using (embed; 0<embed)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (0<embedℚ)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ; embedℚ-*; embedℚ-+)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Exp.Core using (term; term-nonNeg; sucNonZero; sumQ; expPartial)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Laws using (*ℝ-comm; *ℝ-assoc)
open import Real.Interval.Mul.Order using
  (*ℝ-nonNeg; *ℝ-≤-mono; +ℝ-cong; ≤-resp-≈ˡ; ≤-resp-≈ʳ)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using (<⇒≤ℝ; ≤ℝ-refl)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using (recipℝ-pos; embedℚ-recip)
open import Real.Interval.Series.Alternating using (sum-mono)
open import Real.Interval.Series.Core using (sum; sum-nonNeg; sum-mono-step; sum-mono-tail)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)

------------------------------------------------------------------------
-- Terms of the real exponential series
--
-- 实数指数级数的通项

-- termℝ x 0 = 1 and termℝ x (k+1) = termℝ x k * x * (1/(k+1)). The
-- reciprocal is of the embedded increment, whose positivity is
-- `0<embedℚ (embed (suc k)) (0<embed k)`; the definition is a recurrence,
-- so a step is one unfolding.
--
-- termℝ x 0 = 1，termℝ x (k+1) = termℝ x k * x * (1/(k+1))。倒数取自
-- 嵌入的增量，其正性由 0<embedℚ (embed (suc k)) (0<embed k) 给出；定义
-- 是递推，故一步即一次展开。
termℝ : RealI → ℕ → RealI
termℝ x zero    = 1ℝ
termℝ x (suc k) =
  (termℝ x k *ℝ x) *ℝ recipℝ (embedℚ (embed (suc k))) (0<embedℚ (embed (suc k)) (0<embed k))

termℝ-suc : (x : RealI) (k : ℕ)
          → termℝ x (suc k)
            ≡ (termℝ x k *ℝ x) *ℝ recipℝ (embedℚ (embed (suc k))) (0<embedℚ (embed (suc k)) (0<embed k))
termℝ-suc x k = refl

------------------------------------------------------------------------
-- Non-negative arguments give non-negative terms
--
-- 非负自变量给出非负通项

-- The first term is 1 > 0. Each step multiplies two non-negative reals:
-- the running term (induction hypothesis) with x, then that product with
-- the positive reciprocal of the increment.
--
-- 首项是 1 > 0。每一步乘两个非负实数：累计通项（归纳假设）与 x，再把
-- 该乘积乘上增量的正倒数。
termℝ-nonNeg : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (k : ℕ)
             → 0ℝ ≤ℝ termℝ x k
termℝ-nonNeg x 0≤x zero    = <⇒≤ℝ 0ℝ<ℝ1ℝ
termℝ-nonNeg x 0≤x (suc k) =
  *ℝ-nonNeg (termℝ x k *ℝ x)
    (recipℝ (embedℚ (embed (suc k))) (0<embedℚ (embed (suc k)) (0<embed k)))
    (*ℝ-nonNeg (termℝ x k) x (termℝ-nonNeg x 0≤x k) 0≤x)
    (<⇒≤ℝ (recipℝ-pos (embedℚ (embed (suc k)))
      (0<embedℚ (embed (suc k)) (0<embed k))))

------------------------------------------------------------------------
-- Partial sums of the real exponential series
--
-- 实数指数级数的部分和

expPartialℝ : RealI → ℕ → RealI
expPartialℝ x = sum (termℝ x)

expPartialℝ-nonNeg : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (n : ℕ)
                   → 0ℝ ≤ℝ expPartialℝ x n
expPartialℝ-nonNeg x 0≤x = sum-nonNeg (termℝ x) (termℝ-nonNeg x 0≤x)

expPartialℝ-step-mono : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (n : ℕ)
                      → expPartialℝ x n ≤ℝ expPartialℝ x (suc n)
expPartialℝ-step-mono x 0≤x = sum-mono-step (termℝ x) (termℝ-nonNeg x 0≤x)

-- Partial sums increase along any later index, not only the next one.
--
-- 部分和沿任意更后的指标递增，而不只沿后继。
expPartialℝ-index-mono : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (n m : ℕ)
                       → n ≤ℕ m
                       → expPartialℝ x n ≤ℝ expPartialℝ x m
expPartialℝ-index-mono x 0≤x n m n≤m =
  subst (λ k → expPartialℝ x n ≤ℝ expPartialℝ x k)
        (m+[n∸m]≡n n≤m)
        (sum-mono-tail (termℝ x) (termℝ-nonNeg x 0≤x) n (m ∸ n))

------------------------------------------------------------------------
-- Non-negative rationals embed to non-negative reals
--
-- 非负有理数嵌入为非负实数

-- `0ℚ ≤ q` is `¬ (q < 0ℚ)`, and `embedℚ-reflect` turns a putative
-- `embedℚ q < 0ℝ` into `q < 0ℚ`. Note `0ℝ` and `embedℚ 0ℚ` are the same
-- term, so the reflect applies without transport.
--
-- 0ℚ ≤ q 就是 ¬ (q < 0ℚ)，而 embedℚ-reflect 把反设的 embedℚ q < 0ℝ
-- 变成 q < 0ℚ。注意 0ℝ 与 embedℚ 0ℚ 是同一项，故反射不必搬运。
embedℚ-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) → 0ℝ ≤ℝ embedℚ q
embedℚ-nonNeg q 0≤q = λ h → ≤⇒≯ 0≤q (embedℚ-reflect q 0ℚ h)

------------------------------------------------------------------------
-- The shape of an embedded rational step
--
-- 嵌入的有理一步的形状

-- The real step at q is (term q k * q) * (1/(k+1)), so its embedding
-- splits into the embedded running term, the embedded q, and the
-- reciprocal of the embedded increment. This is the arithmetic skeleton
-- shared by both comparisons against a rational bound, proved once here.
--
-- q 处的实数一步是 (term q k * q) * (1/(k+1))，故其嵌入拆成嵌入的
-- 累计通项、嵌入的 q，以及嵌入增量的倒数。这是两个对有理界比较共用
-- 的算术骨架，在此证一次。
embedℚ-term-suc-shape : (q : ℚ) (k : ℕ)
                      → embedℚ (term q (suc k))
                        ≈ℝ (embedℚ (term q k) *ℝ embedℚ q) *ℝ recipℝ (embedℚ (embed (suc k))) (0<embedℚ (embed (suc k)) (0<embed k))
embedℚ-term-suc-shape q k =
  let
    A : RealI
    A = embedℚ (term q k)

    m : RealI
    m = embedℚ q

    s0 : RealI
    s0 = embedℚ (embed (suc k))

    h : 0ℝ <ℝ s0
    h = 0<embedℚ (embed (suc k)) (0<embed k)

    r : RealI
    r = recipℝ s0 h

    step : embedℚ (term q k * _÷_ q (embed (suc k)) {{sucNonZero k}})
             ≈ℝ A *ℝ embedℚ (_÷_ q (embed (suc k)) {{sucNonZero k}})
    step = embedℚ-* (term q k) (_÷_ q (embed (suc k)) {{sucNonZero k}})

    inner : embedℚ (_÷_ q (embed (suc k)) {{sucNonZero k}}) ≈ℝ m *ℝ r
    inner =
      ≈ℝ-trans (embedℚ-* q (1/_ (embed (suc k)) {{sucNonZero k}}))
        (*ℝ-cong ≈ℝ-refl
          (embedℚ-recip (embed (suc k)) ⦃ sucNonZero k ⦄ (0<embed k)))
  in
    ≈ℝ-trans (≈ℝ-trans step (*ℝ-cong ≈ℝ-refl inner))
      (≈ℝ-sym (*ℝ-assoc A m r))
------------------------------------------------------------------------
-- The terms are dominated by the terms of a rational majorant
--
-- 通项被有理优控的通项压制

-- If 0 ≤ x ≤ embedℚ M and M is a non-negative rational, then every term
-- of the series at x is at most the corresponding rational term at M
-- Both products in the step are compared factorwise with `*ℝ-≤-mono`
-- (non-negative factors only), and the reciprocal is rewritten through
-- `embedℚ-recip`, so the two sides carry the same increment.
--
-- 若 0 ≤ x ≤ embedℚ M 且 M 是非负有理数，则 x 处级数的每一通项都不超过
-- M 处对应的有理通项。一步中的两次乘积都用 *ℝ-≤-mono 逐因子比较（只
-- 需非负因子），倒数经 embedℚ-recip 改写，于是两侧带同一个增量。
termℝ-≤-of-bound : (x : RealI) (M : ℚ)
                   (0≤x : 0ℝ ≤ℝ x) (x≤M : x ≤ℝ embedℚ M)
                   (0≤M : 0ℚ ≤ M) (k : ℕ)
                 → termℝ x k ≤ℝ embedℚ (term M k)
termℝ-≤-of-bound x M 0≤x x≤M 0≤M zero = ≤ℝ-refl
termℝ-≤-of-bound x M 0≤x x≤M 0≤M (suc k) =
  let
    a : RealI
    a = termℝ x k

    A : RealI
    A = embedℚ (term M k)

    m : RealI
    m = embedℚ M

    s0 : RealI
    s0 = embedℚ (embed (suc k))

    h : 0ℝ <ℝ s0
    h = 0<embedℚ (embed (suc k)) (0<embed k)

    r : RealI
    r = recipℝ s0 h

    0≤A : 0ℝ ≤ℝ A
    0≤A = embedℚ-nonNeg (term M k) (term-nonNeg M 0≤M k)

    0≤r : 0ℝ ≤ℝ r
    0≤r = <⇒≤ℝ (recipℝ-pos s0 h)

    ih : a ≤ℝ A
    ih = termℝ-≤-of-bound x M 0≤x x≤M 0≤M k

    left : a *ℝ x ≤ℝ A *ℝ x
    left = *ℝ-≤-mono a A x ih 0≤x

    mid₀ : x *ℝ A ≤ℝ m *ℝ A
    mid₀ = *ℝ-≤-mono x m A x≤M 0≤A

    mid₁ : A *ℝ x ≤ℝ m *ℝ A
    mid₁ = ≤-resp-≈ˡ (*ℝ-comm x A) mid₀

    mid : A *ℝ x ≤ℝ A *ℝ m
    mid = ≤-resp-≈ʳ mid₁ (*ℝ-comm m A)

    both : a *ℝ x ≤ℝ A *ℝ m
    both = ≤ℝ-trans left mid

    scaled : (a *ℝ x) *ℝ r ≤ℝ (A *ℝ m) *ℝ r
    scaled = *ℝ-≤-mono (a *ℝ x) (A *ℝ m) r both 0≤r

    shape : embedℚ (term M (suc k)) ≈ℝ (A *ℝ m) *ℝ r
    shape = embedℚ-term-suc-shape M k
  in
    ≤-resp-≈ʳ scaled (≈ℝ-sym shape)
------------------------------------------------------------------------
-- Embedding preserves finite sums
--
-- 嵌入保持有限和

-- Induction on the length: the empty rational sum is 0ℚ whose embedding
-- is 0ℝ, and each step moves the embedding through `embedℚ-+`.
--
-- 对长度归纳：空和是 0ℚ，其嵌入即 0ℝ；每一步用 embedℚ-+ 把嵌入推进
-- 过加法。
embedℚ-sum : (f : ℕ → ℚ) (n : ℕ)
           → embedℚ (sumQ f n) ≈ℝ sum (λ k → embedℚ (f k)) n
embedℚ-sum f zero    = ≈ℝ-refl
embedℚ-sum f (suc n) =
  ≈ℝ-trans (embedℚ-+ (sumQ f n) (f n))
    (+ℝ-cong (embedℚ-sum f n) ≈ℝ-refl)

------------------------------------------------------------------------
-- The partial sums at x are below the embedded rational partial sums
--
-- x 处的部分和低于嵌入的有理部分和

-- Pointwise domination of the terms (termℝ-≤-of-bound) lifts to the
-- partial sums through `sum-mono`, and `embedℚ-sum` identifies the
-- embedded rational partial sum with the real one.
--
-- 通项的逐点优控（termℝ-≤-of-bound）经 sum-mono 抬到部分和，
-- embedℚ-sum 把嵌入的有理部分和与实数和认同。
expPartialℝ-≤-of-bound : (x : RealI) (M : ℚ)
                         (0≤x : 0ℝ ≤ℝ x) (x≤M : x ≤ℝ embedℚ M)
                         (0≤M : 0ℚ ≤ M) (n : ℕ)
                       → expPartialℝ x n ≤ℝ embedℚ (expPartial M n)
expPartialℝ-≤-of-bound x M 0≤x x≤M 0≤M n =
  ≤-resp-≈ʳ
    (sum-mono (termℝ x) (λ k → embedℚ (term M k))
      (λ k → termℝ-≤-of-bound x M 0≤x x≤M 0≤M k) n)
    (≈ℝ-sym (embedℚ-sum (term M) n))
------------------------------------------------------------------------
-- A rational minorant bounds the partial sums from below
--
-- 有理下界从下方界住部分和

-- The symmetric companion of termℝ-≤-of-bound: if embedℚ m ≤ x and m is
-- non-negative, then every embedded rational term is below the real term
-- Both products are compared factorwise again, and the shared step shape
-- keeps the increment identical on the two sides.
--
-- termℝ-≤-of-bound 的对称伙伴：若 embedℚ m ≤ x 且 m 非负，则嵌入的有理
-- 通项低于实数通项。两个乘积仍逐因子比较，共享的一步形状使两侧带同一
-- 增量。
termℝ-≥-of-bound : (x : RealI) (m : ℚ)
                   (0≤m : 0ℚ ≤ m) (m≤x : embedℚ m ≤ℝ x) (k : ℕ)
                 → embedℚ (term m k) ≤ℝ termℝ x k
termℝ-≥-of-bound x m 0≤m m≤x zero = ≤ℝ-refl
termℝ-≥-of-bound x m 0≤m m≤x (suc k) =
  let
    a : RealI
    a = termℝ x k

    A : RealI
    A = embedℚ (term m k)

    m0 : RealI
    m0 = embedℚ m

    s0 : RealI
    s0 = embedℚ (embed (suc k))

    h : 0ℝ <ℝ s0
    h = 0<embedℚ (embed (suc k)) (0<embed k)

    r : RealI
    r = recipℝ s0 h

    0≤x : 0ℝ ≤ℝ x
    0≤x = ≤ℝ-trans (embedℚ-nonNeg m 0≤m) m≤x

    0≤a : 0ℝ ≤ℝ a
    0≤a = termℝ-nonNeg x 0≤x k

    0≤m0 : 0ℝ ≤ℝ m0
    0≤m0 = embedℚ-nonNeg m 0≤m

    0≤r : 0ℝ ≤ℝ r
    0≤r = <⇒≤ℝ (recipℝ-pos s0 h)

    ih : A ≤ℝ a
    ih = termℝ-≥-of-bound x m 0≤m m≤x k

    left : A *ℝ m0 ≤ℝ a *ℝ m0
    left = *ℝ-≤-mono A a m0 ih 0≤m0

    right₀ : m0 *ℝ a ≤ℝ x *ℝ a
    right₀ = *ℝ-≤-mono m0 x a m≤x 0≤a

    right : a *ℝ m0 ≤ℝ a *ℝ x
    right = ≤-resp-≈ʳ (≤-resp-≈ˡ (*ℝ-comm m0 a) right₀) (*ℝ-comm x a)

    both : A *ℝ m0 ≤ℝ a *ℝ x
    both = ≤ℝ-trans left right

    scaled : (A *ℝ m0) *ℝ r ≤ℝ (a *ℝ x) *ℝ r
    scaled = *ℝ-≤-mono (A *ℝ m0) (a *ℝ x) r both 0≤r

    shape : embedℚ (term m (suc k)) ≈ℝ (A *ℝ m0) *ℝ r
    shape = embedℚ-term-suc-shape m k
  in
    ≤-resp-≈ˡ (≈ℝ-sym shape) scaled

expPartialℝ-≥-of-bound : (x : RealI) (m : ℚ)
                         (0≤m : 0ℚ ≤ m) (m≤x : embedℚ m ≤ℝ x) (n : ℕ)
                       → embedℚ (expPartial m n) ≤ℝ expPartialℝ x n
expPartialℝ-≥-of-bound x m 0≤m m≤x n =
  ≤-resp-≈ˡ (≈ℝ-sym (embedℚ-sum (term m) n))
    (sum-mono (λ k → embedℚ (term m k)) (termℝ x)
      (λ k → termℝ-≥-of-bound x m 0≤m m≤x k) n)
------------------------------------------------------------------------
-- The terms increase with the argument
--
-- 通项随自变量增大

-- Induction on k. The step multiplies two comparisons: the running term
-- (induction hypothesis) against a fixed x, then x against y with the
-- factor a_y; the two are chained through `≤ℝ-trans`, and the whole
-- product is multiplied by the positive reciprocal on the right. Note the
-- shift keeps the *same* reciprocal term on both sides, since the
-- increment does not depend on the argument.
--
-- 对 k 归纳。一步中乘两次比较：累计通项（归纳假设）对固定的 x，以及
-- 以 a_y 为因子比较 x 与 y；两者用 ≤ℝ-trans 串起来，再整体右乘增量的
-- 正倒数。注意两侧的倒数是同一项，因为增量不依赖自变量。
termℝ-mono : (x y : RealI) (0≤x : 0ℝ ≤ℝ x) (x≤y : x ≤ℝ y) (k : ℕ)
           → termℝ x k ≤ℝ termℝ y k
termℝ-mono x y 0≤x x≤y zero = ≤ℝ-refl
termℝ-mono x y 0≤x x≤y (suc k) =
  let
    0≤y : 0ℝ ≤ℝ y
    0≤y = ≤ℝ-trans 0≤x x≤y

    0≤ay : 0ℝ ≤ℝ termℝ y k
    0≤ay = termℝ-nonNeg y 0≤y k

    s0 : RealI
    s0 = embedℚ (embed (suc k))

    h : 0ℝ <ℝ s0
    h = 0<embedℚ (embed (suc k)) (0<embed k)

    r : RealI
    r = recipℝ s0 h

    0≤r : 0ℝ ≤ℝ r
    0≤r = <⇒≤ℝ (recipℝ-pos s0 h)

    l₁ : termℝ x k *ℝ x ≤ℝ termℝ y k *ℝ x
    l₁ = *ℝ-≤-mono (termℝ x k) (termℝ y k) x
      (termℝ-mono x y 0≤x x≤y k) 0≤x

    l₂₀ : x *ℝ termℝ y k ≤ℝ y *ℝ termℝ y k
    l₂₀ = *ℝ-≤-mono x y (termℝ y k) x≤y 0≤ay

    l₂ : termℝ y k *ℝ x ≤ℝ termℝ y k *ℝ y
    l₂ = ≤-resp-≈ʳ (≤-resp-≈ˡ (*ℝ-comm x (termℝ y k)) l₂₀)
      (*ℝ-comm y (termℝ y k))

    l : termℝ x k *ℝ x ≤ℝ termℝ y k *ℝ y
    l = ≤ℝ-trans l₁ l₂
  in
    *ℝ-≤-mono (termℝ x k *ℝ x) (termℝ y k *ℝ y) r l 0≤r

------------------------------------------------------------------------
-- The partial sums increase with the argument
--
-- 部分和随自变量增大

-- Pointwise monotonicity of the terms lifts through `sum-mono`.
--
-- 通项的逐点单调性经 sum-mono 抬到部分和。
expPartialℝ-mono : (x y : RealI) (0≤x : 0ℝ ≤ℝ x) (x≤y : x ≤ℝ y) (n : ℕ)
                 → expPartialℝ x n ≤ℝ expPartialℝ y n
expPartialℝ-mono x y 0≤x x≤y n =
  sum-mono (termℝ x) (termℝ y) (λ k → termℝ-mono x y 0≤x x≤y k) n

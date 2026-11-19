------------------------------------------------------------------------
-- Series of real numbers: partial sums and monotonicity
--
-- 实数级数：部分和与单调性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Series.Core where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; _+ℝ_)
open import Real.Interval.ArithLaws using (+ℝ-comm; +ℝ-identityˡ)
open import Real.Interval.Equiv using (≈ℝ-refl)
open import Real.Interval.OrderLe using (≤ℝ-refl; ≤ℝ-resp-≈; ≤ℝ-+-mono)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)

------------------------------------------------------------------------
-- Partial sums
--
-- 部分和

-- This module carries only what is independent of any convergence
-- estimate: the partial sums themselves, non-negativity of partial sums
-- from non-negative terms, and the fact that partial sums grow when the
-- terms are non-negative. Tail estimates (geometric majorants, factorials)
-- live in Real.Interval.Series.Bounds, and the convergence statement is
-- kept out of here on purpose: it needs a locatedness argument on the
-- range of the partial sums, which is exactly what a tail estimate buys.
-- sum f n is the sum of the first n terms, so sum f 0 = 0ℝ and the
-- successor step adds the term of index n.
--
-- 本模块只放与任何收敛估计无关的部分：部分和本身、非负项给出部分和
-- 非负、以及非负项时部分和递增。尾估计（几何优势和阶乘）在
-- Real.Interval.Series.Bounds 中；收敛陈述故意不放在这里：它需要在
-- 部分和的范围上做可定位论证，而可定位正是尾估计带来的东西。
-- sum f n 是前 n 项之和，故 sum f 0 = 0ℝ，后继一步加上下标 n 的项。
sum : (ℕ → RealI) → ℕ → RealI
sum f zero    = 0ℝ
sum f (suc n) = sum f n +ℝ f n

------------------------------------------------------------------------
-- Shifting a summand to the right of the addition
--
-- 把加数移到加法右侧

-- x ≤ x + y holds as soon as y is non-negative. The proof adds 0 on
-- the left and then uses commutativity twice: once to move the summand,
-- once to rewrite the left endpoint 0 + x as x.
--
-- 只要 y 非负就有 x ≤ x + y。证明先在左边加 0，再用两次交换律：
-- 一次移加数，一次把左端点 0 + x 换成 x。
x≤x+y : (x y : RealI) → 0ℝ ≤ℝ y → x ≤ℝ x +ℝ y
x≤x+y x y 0≤y =
  ≤ℝ-resp-≈ (+ℝ-identityˡ x) (+ℝ-comm y x)
    (≤ℝ-+-mono {x = 0ℝ} {y = y} {z = x} 0≤y)

------------------------------------------------------------------------
-- Partial sums of non-negative terms are non-negative
--
-- 非负项的部分和非负

sum-nonNeg : (f : ℕ → RealI) (0≤f : ∀ n → 0ℝ ≤ℝ f n) (n : ℕ)
           → 0ℝ ≤ℝ sum f n
sum-nonNeg f 0≤f zero    = ≤ℝ-refl
sum-nonNeg f 0≤f (suc n) =
  ≤ℝ-trans (0≤f n)
    (≤ℝ-resp-≈ ≈ℝ-refl (+ℝ-comm (f n) (sum f n))
      (x≤x+y (f n) (sum f n) (sum-nonNeg f 0≤f n)))

------------------------------------------------------------------------
-- Non-negative terms make the partial sums increase
--
-- 非负项使部分和递增

sum-mono-step : (f : ℕ → RealI) (0≤f : ∀ n → 0ℝ ≤ℝ f n) (n : ℕ)
              → sum f n ≤ℝ sum f (suc n)
sum-mono-step f 0≤f n = x≤x+y (sum f n) (f n) (0≤f n)

-- Iterated monotonicity: adding d terms can only increase the sum.
--
-- 迭代单调性：再加 d 项只会使和变大。
sum-mono-tail : (f : ℕ → RealI) (0≤f : ∀ n → 0ℝ ≤ℝ f n) (n d : ℕ)
              → sum f n ≤ℝ sum f (n + d)
sum-mono-tail f 0≤f n zero =
  subst (λ k → sum f n ≤ℝ sum f k) (sym (+-identityʳ n)) ≤ℝ-refl
sum-mono-tail f 0≤f n (suc d) =
  subst (λ k → sum f n ≤ℝ sum f k) (sym (+-suc n d))
    (≤ℝ-trans (sum-mono-tail f 0≤f n d)
              (sum-mono-step f 0≤f (n + d)))

------------------------------------------------------------------------
-- Each term is bounded by the partial sum that includes it
--
-- 每一项都被包含它的部分和界住

term-≤-sum : (f : ℕ → RealI) (0≤f : ∀ n → 0ℝ ≤ℝ f n) (n : ℕ)
           → f n ≤ℝ sum f (suc n)
term-≤-sum f 0≤f n =
  ≤ℝ-resp-≈ ≈ℝ-refl (+ℝ-comm (f n) (sum f n))
    (x≤x+y (f n) (sum f n) (sum-nonNeg f 0≤f n))

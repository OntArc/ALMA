------------------------------------------------------------------------
-- Splitting a pair of partial sums across the diagonal
--
-- 把一对部分和拆到对角线上
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Splice where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (n<1+n; <-trans)
open import Data.Rational using (ℚ; 0ℚ; _+_)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import Real.Interval.Rational using (+rearrange)
open import Real.Interval.Exp.Core using (sumQ)
open import Real.Interval.Exp.Conv using (sumQ-tail)
open import Real.Interval.Exp.Lipschitz using (sumQ-add)

------------------------------------------------------------------------
-- A sum with a vanishing head
--
-- 首项为零的和

-- The same summands read one index later, with a zero in front.
--
-- 同一列被加项，整体后移一个指标，并在前面补零。
head0 : (ℕ → ℚ) → ℕ → ℚ
head0 f zero    = 0ℚ
head0 f (suc i) = f i

------------------------------------------------------------------------
-- Regrouping sums
--
-- 和的重排

-- The two sums `A` and `B` under a common bound, rejoined along the
-- diagonal: index zero only sees `B`, every later index sees both.
--
-- 同一界下的两列和 `A`、`B` 沿对角线合并：零指标只见到 `B`，之后的指标两边都见到。
shift-sum : (A B : ℕ → ℚ) (k : ℕ)
          → sumQ A k + sumQ B (suc k)
            ≡ sumQ (λ j → head0 A j + B j) (suc k)
shift-sum A B k =
  trans (cong₂ _+_ (sym (sumQ-tail A (head0 A) k refl (λ i → refl))) refl)
        (sym (sumQ-add (head0 A) B (suc k)))

-- Concatenating two partial sums of length `k+1`: the last term of the
-- first sum is pulled out and both sums are merged along the diagonal.
--
-- 拼接两列长度为 `k+1` 的部分和：第一列和的末项被提到外面，两列沿对角线合并。
splice : (A B : ℕ → ℚ) (k : ℕ)
       → sumQ A (suc k) + sumQ B (suc k)
         ≡ sumQ (λ j → head0 A j + B j) (suc k) + A k
splice A B k =
  trans (+rearrange (sumQ A k) (A k) (sumQ B (suc k)))
        (cong (λ z → z + A k) (shift-sum A B k))

------------------------------------------------------------------------
-- Congruence only on an initial segment
--
-- 只在初始段上相等的同余

-- Two sums agree as soon as the summands agree below the bound.
--
-- 只要被加项在界下相等，两列和就相等。
sumQ-cong-upto : (f g : ℕ → ℚ) (n : ℕ)
               → (∀ i → i < n → f i ≡ g i)
               → sumQ f n ≡ sumQ g n
sumQ-cong-upto f g zero    e = refl
sumQ-cong-upto f g (suc n) e =
  cong₂ _+_ (sumQ-cong-upto f g n (λ i i<n → e i (<-trans i<n (n<1+n n))))
           (e n (n<1+n n))

------------------------------------------------------------------------
-- Partial sums under multiplication
--
-- 乘法下的部分和
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Conv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational using (ℚ; _+_; _*_; 0ℚ)
open import Data.Rational.Properties using
  (*-zeroˡ; *-zeroʳ; *-distribˡ-+; *-distribʳ-+; +-identityˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; trans)

open import Real.Interval.Exp.Core using (sumQ; term; expPartial)

------------------------------------------------------------------------
-- Distributing a factor over a partial sum
--
-- 把因子分配到部分和上

-- Multiplication on the left distributes over every term of the sum.
--
-- 左乘分配到和的每一项。
*-sumQˡ : (y : ℚ) (f : ℕ → ℚ) (n : ℕ)
       → y * sumQ f n ≡ sumQ (λ k → y * f k) n
*-sumQˡ y f zero    = *-zeroʳ y
*-sumQˡ y f (suc n) =
  trans (*-distribˡ-+ y (sumQ f n) (f n))
        (cong₂ _+_ (*-sumQˡ y f n) refl)

-- Multiplication on the right distributes over every term of the sum.
--
-- 右乘分配到和的每一项。
*-sumQʳ : (f : ℕ → ℚ) (n : ℕ) (y : ℚ)
       → sumQ f n * y ≡ sumQ (λ k → f k * y) n
*-sumQʳ f zero    y = *-zeroˡ y
*-sumQʳ f (suc n) y =
  trans (*-distribʳ-+ y (sumQ f n) (f n))
        (cong₂ _+_ (*-sumQʳ f n y) refl)

------------------------------------------------------------------------
-- The product of two partial sums as a double sum
--
-- 两个部分和之积作为二重和

-- Multiplying one sum by another expands into the sum of all pairwise
-- products, indexed by the two summation variables.
--
-- 一个和乘以另一个和，展开为按两个求和变量索引的全部两两乘积之和。
mul-sumQ : (f g : ℕ → ℚ) (n m : ℕ)
         → sumQ f n * sumQ g m ≡ sumQ (λ i → sumQ (λ j → f i * g j) m) n
mul-sumQ f g zero    m = *-zeroˡ (sumQ g m)
mul-sumQ f g (suc n) m =
  trans (*-distribʳ-+ (sumQ g m) (sumQ f n) (f n))
        (cong₂ _+_ (mul-sumQ f g n m) (*-sumQˡ (f n) g m))

-- The product of the two truncated exponential series, expanded pairwise.
--
-- 两条截断指数级数之积，按项两两展开。
expPartial-mul : (p q : ℚ) (n : ℕ)
               → expPartial p n * expPartial q n
                 ≡ sumQ (λ i → sumQ (λ j → term p i * term q j) n) n
expPartial-mul p q n = mul-sumQ (term p) (term q) n n

------------------------------------------------------------------------
-- Shifting a partial sum by one index
--
-- 部分和的指标平移

-- If the head term of a sum vanishes, the sum over the tail is the
-- original sum with the indices renamed.
--
-- 若一列和的首项为零，那么对尾部求和就是把指标重命名后的原和。
sumQ-tail : (f h : ℕ → ℚ) (n : ℕ)
          → h zero ≡ 0ℚ
          → (∀ i → h (suc i) ≡ f i)
          → sumQ h (suc n) ≡ sumQ f n
sumQ-tail f h zero h0 hs = trans (cong (λ z → 0ℚ + z) h0) (+-identityˡ 0ℚ)
sumQ-tail f h (suc n) h0 hs =
  cong₂ _+_ (sumQ-tail f h n h0 hs) (hs n)

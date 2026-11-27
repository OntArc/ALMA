------------------------------------------------------------------------
-- The diagonal summands of the exponential product
--
-- 指数乘积的对角被加项
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Diag where

open import Data.Nat using (ℕ; zero; suc; pred; _∸_)
open import Data.Rational using (ℚ; _+_; _*_)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; trans)

open import Base.RationalRing using (swap-mid)
open import Real using (embed; ε)
open import Real.Interval.Exp.Core using (term; term-suc)
open import Real.Interval.Exp.Factorial using (invProd; term-factorial)
open import Real.Interval.Rational using (powQ)

------------------------------------------------------------------------
-- Subtraction of two successors
--
-- 两个后继的减法

-- Cancelling one successor on each side of the subtraction.
--
-- 在减法的两侧各消去一个后继。
∸-suc-suc : (i k : ℕ) → suc k ∸ suc i ≡ k ∸ i
∸-suc-suc i k = refl

------------------------------------------------------------------------
-- The diagonal summand at the rational level
--
-- 有理层的对角被加项

-- The product of the `i`-th and the `k-i`-th terms, written in closed form.
--
-- 第 `i` 项与第 `k-i` 项之积，按闭式写出。
diag : (p q : ℚ) (k i : ℕ) → ℚ
diag p q k i = (powQ p i * powQ q (k ∸ i)) * (invProd i * invProd (k ∸ i))

-- Both factors are exponents over factorials, so the product is the
-- diagonal summand.
--
-- 两个因子都是幂除以阶乘，故其积就是对角被加项。
diag-correct : (p q : ℚ) (k i : ℕ) → term p i * term q (k ∸ i) ≡ diag p q k i
diag-correct p q k i =
  trans (cong₂ _*_ (term-factorial p i) (term-factorial q (k ∸ i)))
        (swap-mid (powQ p i) (invProd i) (powQ q (k ∸ i)) (invProd (k ∸ i)))

------------------------------------------------------------------------
-- One more precision on either side
--
-- 两侧各进一步精度

-- Splitting the diagonal summand multiplied by the next precision: the
-- factor `p+q` is distributed and each half is absorbed into one exponent.
--
-- 对角被加项乘以下一精度后的拆分：因子 `p+q` 分配到两半，各自并进指数。
step-split : (p q : ℚ) (k i : ℕ)
           → diag p q k i * ((p + q) * ε k)
             ≡ ((powQ p (suc i) * powQ q (k ∸ i))
                 * (invProd i * invProd (k ∸ i))) * ε k
               + ((powQ p i * powQ q (suc (k ∸ i)))
                   * (invProd i * invProd (k ∸ i))) * ε k
step-split p q k i =
  solve 7 (λ A B C D pp qq E →
             (((A :* B) :* (C :* D)) :* ((pp :+ qq) :* E))
               := ((((pp :* A) :* B) :* (C :* D)) :* E)
                  :+ (((A :* (qq :* B)) :* (C :* D)) :* E))
    refl (powQ p i) (powQ q (k ∸ i)) (invProd i) (invProd (k ∸ i)) p q (ε k)

------------------------------------------------------------------------
-- The recurrence of a term
--
-- 通项的递推

-- The recurrence of `term` at one precision, with the division unfolded
-- into a multiplication by the reciprocal.
--
-- `term` 在一层精度上的递推，把除法展开为乘以倒数。
term-suc-step : (h : ℚ) (k : ℕ) → term h (suc k) ≡ term h k * (h * ε k)
term-suc-step h k = term-suc h k

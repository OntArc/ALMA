------------------------------------------------------------------------
-- Closed form of the exponential terms
--
-- 指数通项的闭式
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Factorial where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; 1/_; NonZero; Positive)
open import Data.Rational.Base using (positive; _÷_)
open import Data.Rational.Properties using
  (*-assoc; *-comm; *-identityˡ; *-identityʳ; *-inverseˡ; pos⇒nonZero; pos*pos⇒pos)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1; swap-mid)
open import Real using (embed; embed-suc-pos; embed-+-hom; ε)
open import Real.Interval.Rational using (powQ; recip-*-hom)
open import Real.Interval.Exp.Core using (term; term-suc)

------------------------------------------------------------------------
-- Factorials as rational products
--
-- 阶乘作为有理数乘积

-- The product of the first `k` positive integers, embedded into ℚ; the
-- recurrence keeps the embedding multiplicative step by step, which is
-- what the closed form needs of the denominator.
--
-- 前 `k` 个正整数之积嵌入 ℚ；递推逐步保持嵌入的乘法性，这正是闭式对
-- 分母所需。
prod : ℕ → ℚ
prod zero    = 1ℚ
prod (suc k) = prod k * embed (suc k)

prod-suc : (k : ℕ) → prod (suc k) ≡ prod k * embed (suc k)
prod-suc k = refl

prod-pos : (k : ℕ) → Positive (prod k)
prod-pos zero    = positive 0<1
prod-pos (suc k) = pos*pos⇒pos (prod k) {{prod-pos k}} (embed (suc k)) {{embed-suc-pos}}

prod-nonZero : (k : ℕ) → NonZero (prod k)
prod-nonZero k = pos⇒nonZero (prod k) {{prod-pos k}}

------------------------------------------------------------------------
-- Reciprocal factorials
--
-- 阶乘的倒数

invProd : (k : ℕ) → ℚ
invProd k = (1/ prod k) ⦃ prod-nonZero k ⦄

-- Multiplying the reciprocal factorial by the next precision produces the
-- next reciprocal factorial; this is `recip-*-hom` read backwards.
--
-- 阶乘倒数的下一个精度相乘得到下一个阶乘倒数；这是反向读的 `recip-*-hom`。
invProd-suc : (k : ℕ) → invProd k * ε k ≡ invProd (suc k)
invProd-suc k =
  sym (recip-*-hom (prod k) (embed (suc k))
        ⦃ prod-nonZero k ⦄
        ⦃ pos⇒nonZero (embed (suc k)) ⦃ embed-suc-pos ⦄ ⦄
        ⦃ prod-nonZero (suc k) ⦄)

------------------------------------------------------------------------
-- Cancelling one level of the denominator
--
-- 消去一层分母

-- The embedded successor and the reciprocal of the same precision cancel.
--
-- 嵌入的后继与其同精度的倒数相消。
embed-ε : (k : ℕ) → embed (suc k) * ε k ≡ 1ℚ
embed-ε k =
  trans (*-comm (embed (suc k)) (ε k))
        (*-inverseˡ (embed (suc k))
          ⦃ pos⇒nonZero (embed (suc k)) ⦃ embed-suc-pos ⦄ ⦄)

-- Multiplying the reciprocal factorial by the next integer cancels that
-- integer against the factorial, leaving the previous reciprocal factorial.
--
-- 阶乘倒数乘以紧邻的整数，把该整数从阶乘里约掉，剩下前一级的阶乘倒数。
invProd-mul-embed : (k : ℕ) → invProd (suc k) * embed (suc k) ≡ invProd k
invProd-mul-embed k = begin
  invProd (suc k) * embed (suc k)
    ≡⟨ cong (λ z → z * embed (suc k)) (sym (invProd-suc k)) ⟩
  (invProd k * ε k) * embed (suc k)
    ≡⟨ *-assoc (invProd k) (ε k) (embed (suc k)) ⟩
  invProd k * (ε k * embed (suc k))
    ≡⟨ cong (invProd k *_) (trans (*-comm (ε k) (embed (suc k))) (embed-ε k)) ⟩
  invProd k * 1ℚ
    ≡⟨ *-identityʳ (invProd k) ⟩
  invProd k ∎

------------------------------------------------------------------------
-- Closed form of a term
--
-- 通项的闭式

termClosed : (q : ℚ) (k : ℕ) → ℚ
termClosed q k = powQ q k * invProd k

-- The recurrence multiplies in one factor `q` and one denominator `k+1`
-- per step, so it produces `q^k` over the factorial, by induction.
--
-- 递推每一步乘进一个因子 `q` 与一个分母 `k+1`，故归纳得 `q^k` 除以阶乘。
term-factorial : (q : ℚ) (k : ℕ) → term q k ≡ termClosed q k
term-factorial q zero = begin
  term q zero
    ≡⟨⟩
  1ℚ
    ≡⟨ sym (*-identityˡ 1ℚ) ⟩
  1ℚ * 1ℚ
    ≡⟨⟩
  termClosed q zero ∎
term-factorial q (suc k) = begin
  term q (suc k)
    ≡⟨ term-suc q k ⟩
  term q k * (q ÷ embed (suc k))
    ≡⟨ cong₂ _*_ (term-factorial q k) refl ⟩
  termClosed q k * (q ÷ embed (suc k))
    ≡⟨ swap-mid (powQ q k) (invProd k) q (ε k) ⟩
  (powQ q k * q) * (invProd k * ε k)
    ≡⟨ cong₂ _*_ (*-comm (powQ q k) q) (invProd-suc k) ⟩
  (q * powQ q k) * invProd (suc k)
    ≡⟨⟩
  termClosed q (suc k) ∎

------------------------------------------------------------------------
-- The binomial step of the coefficients
--
-- 系数的二项递推

-- Reading the reciprocal factorial backwards: one level up means one more
-- embedded factor in front.
--
-- 反向读阶乘倒数：升一级就是在前面多一个嵌入因子。
invProd-embed : (i : ℕ) → invProd i ≡ embed (suc i) * invProd (suc i)
invProd-embed i =
  trans (sym (invProd-mul-embed i)) (*-comm (invProd (suc i)) (embed (suc i)))

-- Regrouping the two products that share the trailing precision.
--
-- 重排两个共享末尾精度的乘积。
regroup : (a b c v x : ℚ)
        → ((a * b) * c) * x + (b * (c * v)) * x
          ≡ (b * c) * ((a + v) * x)
regroup a b c v x =
  solve 5 (λ a b c v x →
             (((a :* b) :* c) :* x) :+ ((b :* (c :* v)) :* x)
               := ((b :* c) :* ((a :+ v) :* x)))
    refl a b c v x

-- Extending one level to the left or to the right of the factorial gives
-- the two summands whose sum is the coefficient of the next level.
--
-- 把一层因子分别补在阶乘左边与右边，所得两加项之和正是下一层的系数。
coeff-step : (i m : ℕ)
           → (invProd i * invProd (suc m)) * ε (i +ℕ suc m)
             + (invProd (suc i) * invProd m) * ε (i +ℕ suc m)
             ≡ invProd (suc i) * invProd (suc m)
coeff-step i m = begin
  (invProd i * invProd (suc m)) * ε (i +ℕ suc m)
    + (invProd (suc i) * invProd m) * ε (i +ℕ suc m)
    ≡⟨ cong (λ z → (z * invProd (suc m)) * ε (i +ℕ suc m)
                     + (invProd (suc i) * invProd m) * ε (i +ℕ suc m))
           (invProd-embed i) ⟩
  ((embed (suc i) * invProd (suc i)) * invProd (suc m)) * ε (i +ℕ suc m)
    + (invProd (suc i) * invProd m) * ε (i +ℕ suc m)
    ≡⟨ cong (λ z → ((embed (suc i) * invProd (suc i)) * invProd (suc m))
                     * ε (i +ℕ suc m)
                     + (invProd (suc i) * z) * ε (i +ℕ suc m))
           (sym (invProd-mul-embed m)) ⟩
  ((embed (suc i) * invProd (suc i)) * invProd (suc m)) * ε (i +ℕ suc m)
    + (invProd (suc i) * (invProd (suc m) * embed (suc m)))
        * ε (i +ℕ suc m)
    ≡⟨ regroup (embed (suc i)) (invProd (suc i)) (invProd (suc m))
              (embed (suc m)) (ε (i +ℕ suc m)) ⟩
  (invProd (suc i) * invProd (suc m))
    * ((embed (suc i) + embed (suc m)) * ε (i +ℕ suc m))
    ≡⟨ cong ((invProd (suc i) * invProd (suc m)) *_)
           (cong (λ z → z * ε (i +ℕ suc m))
                 (sym (embed-+-hom (suc i) (suc m)))) ⟩
  (invProd (suc i) * invProd (suc m))
    * (embed (suc i +ℕ suc m) * ε (i +ℕ suc m))
    ≡⟨ cong ((invProd (suc i) * invProd (suc m)) *_) (embed-ε (i +ℕ suc m)) ⟩
  (invProd (suc i) * invProd (suc m)) * 1ℚ
    ≡⟨ *-identityʳ (invProd (suc i) * invProd (suc m)) ⟩
  invProd (suc i) * invProd (suc m) ∎

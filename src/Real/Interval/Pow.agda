------------------------------------------------------------------------
-- Powers of interval reals
--
-- 区间实数的幂
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Pow where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using
  (*ℝ-comm; *ℝ-assoc; *ℝ-identityˡ; *ℝ-identityʳ; *ℝ-zeroˡ)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using
  (pos*pos; *ℝ-nonNeg; *ℝ-≤-mono; ≤-resp-≈ˡ; ≤-resp-≈ʳ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using (≤ℝ-refl; <⇒≤ℝ)
open import Real.Interval.Reasoning.Equiv using (beginℝ_; _≈ℝ⟨_⟩_; _∎ℝ)

------------------------------------------------------------------------
-- Natural powers
--
-- 自然数次幂

infixr 8 _^ℝ_

-- Powers of interval reals.
--
-- 区间实数的幂。
_^ℝ_ : RealI → ℕ → RealI
x ^ℝ zero  = 1ℝ
x ^ℝ suc n = (x ^ℝ n) *ℝ x

------------------------------------------------------------------------
-- Structural laws
--
-- 结构律

-- The zeroth power is one.
--
-- 零次幂为一。
^ℝ-zero : (x : RealI) → x ^ℝ 0 ≈ℝ 1ℝ
^ℝ-zero x = ≈ℝ-refl

-- One step of the recursion, definitionally.
--
-- 递归的一步，按定义为等。
^ℝ-suc : (x : RealI) (n : ℕ) → x ^ℝ suc n ≈ℝ (x ^ℝ n) *ℝ x
^ℝ-suc x n = ≈ℝ-refl

-- The first power is the base.
--
-- 一次幂等于底数。
^ℝ-one : (x : RealI) → x ^ℝ 1 ≈ℝ x
^ℝ-one x = *ℝ-identityˡ x

-- The second power is the square.
--
-- 二次幂为平方。
^ℝ-two : (x : RealI) → x ^ℝ 2 ≈ℝ x *ℝ x
^ℝ-two x =
  beginℝ
    (1ℝ *ℝ x) *ℝ x
      ≈ℝ⟨ *ℝ-cong (*ℝ-identityˡ x) ≈ℝ-refl ⟩
    x *ℝ x
  ∎ℝ

------------------------------------------------------------------------
-- Congruence in the base
--
-- 底数上的同余

^ℝ-cong : {x y : RealI} → x ≈ℝ y → (n : ℕ) → x ^ℝ n ≈ℝ y ^ℝ n
^ℝ-cong {x} {y} x≈y zero = ≈ℝ-refl
^ℝ-cong {x} {y} x≈y (suc n) =
  *ℝ-cong (^ℝ-cong x≈y n) x≈y

------------------------------------------------------------------------
-- Positivity
--
-- 正性

-- A positive base has positive powers.
--
-- 正底数的任意次幂为正。
^ℝ-pos : (x : RealI) → 0ℝ <ℝ x → (n : ℕ) → 0ℝ <ℝ x ^ℝ n
^ℝ-pos x 0<x zero = 0ℝ<ℝ1ℝ
^ℝ-pos x 0<x (suc n) = pos*pos (x ^ℝ n) x (^ℝ-pos x 0<x n) 0<x

------------------------------------------------------------------------
-- Additive law for exponents
--
-- 指数加法律

-- x^(m+n) equals x^m * x^n. Induction on m uses associativity, commutativity
-- and the unit law only; no error analysis is needed.
--
-- x^(m+n) 等于 x^m * x^n。对 m 归纳，只用到结合律、交换律与单位律，
-- 不需要误差分析。
^ℝ-+ : (x : RealI) (m n : ℕ) → x ^ℝ (m + n) ≈ℝ (x ^ℝ m) *ℝ (x ^ℝ n)
^ℝ-+ x zero n = ≈ℝ-sym (*ℝ-identityˡ (x ^ℝ n))
^ℝ-+ x (suc m) n =
  beginℝ
    (x ^ℝ (m + n)) *ℝ x
      ≈ℝ⟨ *ℝ-cong (^ℝ-+ x m n) ≈ℝ-refl ⟩
    ((x ^ℝ m) *ℝ (x ^ℝ n)) *ℝ x
      ≈ℝ⟨ *ℝ-assoc (x ^ℝ m) (x ^ℝ n) x ⟩
    (x ^ℝ m) *ℝ ((x ^ℝ n) *ℝ x)
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (*ℝ-comm (x ^ℝ n) x) ⟩
    (x ^ℝ m) *ℝ (x *ℝ (x ^ℝ n))
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc (x ^ℝ m) x (x ^ℝ n)) ⟩
    ((x ^ℝ m) *ℝ x) *ℝ (x ^ℝ n)
  ∎ℝ

------------------------------------------------------------------------
-- Power of a product
--
-- 乘积的幂

-- (x*y)^n equals x^n * y^n.
--
-- (x*y)^n 等于 x^n * y^n。
^ℝ-* : (x y : RealI) (n : ℕ) → (x *ℝ y) ^ℝ n ≈ℝ (x ^ℝ n) *ℝ (y ^ℝ n)
^ℝ-* x y zero = ≈ℝ-sym (*ℝ-identityˡ 1ℝ)
^ℝ-* x y (suc n) =
  beginℝ
    ((x *ℝ y) ^ℝ n) *ℝ (x *ℝ y)
      ≈ℝ⟨ *ℝ-cong (^ℝ-* x y n) ≈ℝ-refl ⟩
    ((x ^ℝ n) *ℝ (y ^ℝ n)) *ℝ (x *ℝ y)
      ≈ℝ⟨ *ℝ-assoc (x ^ℝ n) (y ^ℝ n) (x *ℝ y) ⟩
    (x ^ℝ n) *ℝ ((y ^ℝ n) *ℝ (x *ℝ y))
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym (*ℝ-assoc (y ^ℝ n) x y)) ⟩
    (x ^ℝ n) *ℝ (((y ^ℝ n) *ℝ x) *ℝ y)
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl
            (*ℝ-cong (*ℝ-comm (y ^ℝ n) x) ≈ℝ-refl) ⟩
    (x ^ℝ n) *ℝ ((x *ℝ (y ^ℝ n)) *ℝ y)
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (*ℝ-assoc x (y ^ℝ n) y) ⟩
    (x ^ℝ n) *ℝ (x *ℝ ((y ^ℝ n) *ℝ y))
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc (x ^ℝ n) x ((y ^ℝ n) *ℝ y)) ⟩
    ((x ^ℝ n) *ℝ x) *ℝ ((y ^ℝ n) *ℝ y)
  ∎ℝ

------------------------------------------------------------------------
-- Powers of one
--
-- 一的幂

-- Every power of one is one.
--
-- 一的任意次幂为一。
^ℝ-one-base : (n : ℕ) → 1ℝ ^ℝ n ≈ℝ 1ℝ
^ℝ-one-base zero = ≈ℝ-refl
^ℝ-one-base (suc n) =
  beginℝ
    (1ℝ ^ℝ n) *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-cong (^ℝ-one-base n) ≈ℝ-refl ⟩
    1ℝ *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-identityʳ 1ℝ ⟩
    1ℝ
  ∎ℝ

------------------------------------------------------------------------
-- Power and base commute
--
-- 幂与底数可交换次序

-- x^(n+1) is x * x^n as well.
--
-- x^(n+1) 也等于 x * x^n。
^ℝ-suc-comm : (x : RealI) (n : ℕ) → x ^ℝ suc n ≈ℝ x *ℝ (x ^ℝ n)
^ℝ-suc-comm x n = *ℝ-comm (x ^ℝ n) x

------------------------------------------------------------------------
-- Power of a power
--
-- 幂的幂

-- (x^m)^n equals x^(n*m). The index is written with the outer exponent on
-- the left so that the successor step stays definitional.
--
-- (x^m)^n 等于 x^(n*m)。指数写成外层幂次在左，使后继步保持定义相等。
^ℝ-pow : (x : RealI) (m n : ℕ) → (x ^ℝ m) ^ℝ n ≈ℝ x ^ℝ (n * m)
^ℝ-pow x m zero = ≈ℝ-refl
^ℝ-pow x m (suc n) =
  beginℝ
    ((x ^ℝ m) ^ℝ n) *ℝ (x ^ℝ m)
      ≈ℝ⟨ *ℝ-cong (^ℝ-pow x m n) ≈ℝ-refl ⟩
    (x ^ℝ (n * m)) *ℝ (x ^ℝ m)
      ≈ℝ⟨ *ℝ-comm (x ^ℝ (n * m)) (x ^ℝ m) ⟩
    (x ^ℝ m) *ℝ (x ^ℝ (n * m))
      ≈ℝ⟨ ≈ℝ-sym (^ℝ-+ x m (n * m)) ⟩
    x ^ℝ (m + n * m)
  ∎ℝ

------------------------------------------------------------------------
-- Powers of a vanishing base
--
-- 消失底数的幂

-- A helper: any power of zero, multiplied by zero, is zero.
--
-- 辅助引理：零的任意次幂再乘零仍为零。
^ℝ-zero-mul : (n : ℕ) → (0ℝ ^ℝ n) *ℝ 0ℝ ≈ℝ 0ℝ
^ℝ-zero-mul zero = *ℝ-identityˡ 0ℝ
^ℝ-zero-mul (suc n) =
  beginℝ
    ((0ℝ ^ℝ n) *ℝ 0ℝ) *ℝ 0ℝ
      ≈ℝ⟨ *ℝ-cong (^ℝ-zero-mul n) ≈ℝ-refl ⟩
    0ℝ *ℝ 0ℝ
      ≈ℝ⟨ *ℝ-zeroˡ 0ℝ ⟩
    0ℝ
  ∎ℝ

-- For a base equal to zero, every positive power vanishes.
--
-- 底数为零时，一切正整数次幂为零。
^ℝ-of-zero : (x : RealI) → x ≈ℝ 0ℝ → (n : ℕ) → x ^ℝ suc n ≈ℝ 0ℝ
^ℝ-of-zero x x≈0 n =
  beginℝ
    (x ^ℝ n) *ℝ x
      ≈ℝ⟨ *ℝ-cong (^ℝ-cong x≈0 n) x≈0 ⟩
    (0ℝ ^ℝ n) *ℝ 0ℝ
      ≈ℝ⟨ ^ℝ-zero-mul n ⟩
    0ℝ
  ∎ℝ

------------------------------------------------------------------------
-- Order
--
-- 序

-- Powers of a non-negative base are non-negative, and the power operation
-- is monotone in the base on non-negative reals. Both are inductions on the
-- exponent using only the order laws of multiplication.
--
-- 非负底数的各次幂非负，且幂运算在非负实数上对底数单调。两者都对指数
-- 归纳，只用乘法的序律。
^ℝ-nonNeg : (x : RealI) → 0ℝ ≤ℝ x → (n : ℕ) → 0ℝ ≤ℝ x ^ℝ n
^ℝ-nonNeg x 0≤x zero = <⇒≤ℝ 0ℝ<ℝ1ℝ
^ℝ-nonNeg x 0≤x (suc n) =
  *ℝ-nonNeg (x ^ℝ n) x (^ℝ-nonNeg x 0≤x n) 0≤x

^ℝ-mono : (x y : RealI) → 0ℝ ≤ℝ x → x ≤ℝ y →
  (n : ℕ) → x ^ℝ n ≤ℝ y ^ℝ n
^ℝ-mono x y 0≤x x≤y zero = ≤ℝ-refl
^ℝ-mono x y 0≤x x≤y (suc n) =
  let
    ih : x ^ℝ n ≤ℝ y ^ℝ n
    ih = ^ℝ-mono x y 0≤x x≤y n

    left : (x ^ℝ n) *ℝ x ≤ℝ (y ^ℝ n) *ℝ x
    left = *ℝ-≤-mono (x ^ℝ n) (y ^ℝ n) x ih 0≤x

    0≤y : 0ℝ ≤ℝ y
    0≤y = ≤ℝ-trans 0≤x x≤y

    raw : x *ℝ (y ^ℝ n) ≤ℝ y *ℝ (y ^ℝ n)
    raw = *ℝ-≤-mono x y (y ^ℝ n) x≤y (^ℝ-nonNeg y 0≤y n)

    right : (y ^ℝ n) *ℝ x ≤ℝ (y ^ℝ n) *ℝ y
    right =
      ≤-resp-≈ʳ
        (≤-resp-≈ˡ (*ℝ-comm x (y ^ℝ n)) raw)
        (*ℝ-comm y (y ^ℝ n))
  in
    ≤ℝ-trans left right

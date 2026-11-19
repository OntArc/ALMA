------------------------------------------------------------------------
-- Series: tails, splitting, and the geometric closed form
--
-- 级数：尾部、拆分与几何闭式
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Series.Bounds where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties as ℚP using
  (+-assoc; +-identityˡ; +-mono-≤; +-monoʳ-≤; ≤-refl; ≤-trans; *-comm
  ; *-distribˡ-+; *-identityʳ; *-zeroʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (2ℚ; half; 0≤embed)
open import Real.IntervalEquiv using (recipPow2)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; _+ℝ_)
open import Real.Interval.ArithLaws using (+ℝ-comm; +ℝ-assoc; +ℝ-identityʳ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Kit using
  (recipPow2-mul; 0≤recipPow2; *-mono-≤-nonNeg; add-self; two-half)
open import Real.Interval.Mul.Order using (+ℝ-cong)
open import Real.Interval.OrderLe using (≤ℝ-refl; ≤ℝ-resp-≈)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.Series.Core using (sum; x≤x+y)

------------------------------------------------------------------------
-- Tail sums
--
-- 尾部部分和

-- tail f n d is the sum of d terms starting at index n, so that
-- sum f (n + d) splits into sum f n plus the tail.
--
-- tail f n d 是从下标 n 起的 d 项之和，使得 sum f (n + d) 拆成
-- sum f n 加尾部。
tail : (ℕ → RealI) → ℕ → ℕ → RealI
tail f n zero    = 0ℝ
tail f n (suc d) = tail f n d +ℝ f (n +ℕ d)

------------------------------------------------------------------------
-- Splitting a partial sum
--
-- 拆分部分和

-- The split isolates the tail, and every later estimate multiplies the
-- tail, so the tail is where the work happens; the ℚ closed form
--     Σ_{k<n} recipPow2 k + 2 * recipPow2 n ≡ 2
-- is the arithmetic skeleton behind those estimates.
--
-- 拆分把尾项隔离出来，之后每条估计都是拿尾部乘以一个量，工作都发生在尾部；
-- ℚ 闭式
--     Σ_{k<n} recipPow2 k + 2 * recipPow2 n ≡ 2
-- 是这些估计背后的算术骨架。
sum-split : (f : ℕ → RealI) (n d : ℕ)
          → sum f (n +ℕ d) ≈ℝ sum f n +ℝ tail f n d
sum-split f n zero =
  subst (λ k → sum f k ≈ℝ sum f n +ℝ 0ℝ) (sym (+-identityʳ n))
    (≈ℝ-sym (+ℝ-identityʳ (sum f n)))
sum-split f n (suc d) =
  subst (λ k → sum f k ≈ℝ sum f n +ℝ tail f n (suc d))
    (sym (+-suc n d))
    (≈ℝ-trans (+ℝ-cong (sum-split f n d) ≈ℝ-refl)
               (+ℝ-assoc (sum f n) (tail f n d) (f (n +ℕ d))))

------------------------------------------------------------------------
-- Tails of non-negative terms are non-negative
--
-- 非负项的尾部非负

tail-nonNeg : (f : ℕ → RealI) (0≤f : ∀ n → 0ℝ ≤ℝ f n) (n d : ℕ)
            → 0ℝ ≤ℝ tail f n d
tail-nonNeg f 0≤f n zero    = ≤ℝ-refl
tail-nonNeg f 0≤f n (suc d) =
  ≤ℝ-trans (0≤f (n +ℕ d))
    (≤ℝ-resp-≈ ≈ℝ-refl (+ℝ-comm (f (n +ℕ d)) (tail f n d))
      (x≤x+y (f (n +ℕ d)) (tail f n d) (tail-nonNeg f 0≤f n d)))

------------------------------------------------------------------------
-- Geometric partial sums over ℚ
--
-- ℚ 上的几何部分和

-- geom n is the mass of the first n halvings. The closed form below is
-- the telescoped one: the predecessor relationship
-- recipPow2 (suc n) ≡ recipPow2 n * half turns the new term into a copy
-- of the old one once doubled, which is what makes the induction go
-- through without any subtraction.
--
-- geom n 是前 n 次折半的质量。下面的闭式是伸缩式：前驱关系
-- recipPow2 (suc n) ≡ recipPow2 n * half 使新项在加倍后成为旧项的一份
-- 拷贝，这正是归纳无需减法即可通过的原因。
geom : ℕ → ℚ
geom zero    = 0ℚ
geom (suc n) = geom n + recipPow2 n

------------------------------------------------------------------------
-- The first halving is half
--
-- 第一次折半就是 half

recipPow2-1 : recipPow2 1 ≡ half
recipPow2-1 = refl

recipPow2-0 : recipPow2 0 ≡ 1ℚ
recipPow2-0 = refl

------------------------------------------------------------------------
-- Successor ratio
--
-- 后继比值

-- recipPow2 (suc n) ≡ recipPow2 n * half, obtained from recipPow2-mul at
-- (n, 1) after matching ℕ addition with suc.
--
-- 由 recipPow2-mul 在 (n, 1) 处、再把 ℕ 加法与 suc 对上得到。
recipPow2-suc : (n : ℕ) → recipPow2 (suc n) ≡ recipPow2 n * half
recipPow2-suc n =
  trans (subst (λ k → recipPow2 k ≡ recipPow2 n * recipPow2 1)
                 (trans (+-suc n zero) (cong suc (+-identityʳ n)))
                 (recipPow2-mul n 1))
        (cong (recipPow2 n *_) recipPow2-1)

------------------------------------------------------------------------
-- Doubling reverses the halving
--
-- 加倍抵消折半

-- 2ℚ * (r * half) ≡ r. Note that 2ℚ is Real's embed 2, so 2ℚ≡1+1 is
-- needed explicitly; this is also why 2ℚ*half≡1 lives in Kit.
--
-- 2ℚ * (r * half) ≡ r。注意 2ℚ 是 Real 里的 embed 2，所以 2ℚ≡1+1
-- 必须显式用上；这也是 2ℚ*half≡1 落在 Kit 里的原因。
two-mul : (r : ℚ) → 2ℚ * (r * half) ≡ r
two-mul r = trans (sym (add-self (r * half))) (two-half r)

------------------------------------------------------------------------
-- Two is one plus one
--
-- 二是两个一

-- 2ℚ * r ≡ r + r, by moving 2ℚ≡1+1 under the product and distributing.
--
-- 2ℚ * r ≡ r + r：先把 2ℚ≡1+1 挪进乘积、再分配。
two-mul-add : (r : ℚ) → 2ℚ * r ≡ r + r
two-mul-add r = sym (add-self r)

------------------------------------------------------------------------
-- Closed form of the geometric partial sum
--
-- 几何部分和的闭式

-- geom n + 2ℚ * recipPow2 n ≡ 2ℚ. The base case is 0 + 2 * 1 ≡ 2; the
-- step replaces the new term by a double of the old one via two-mul,
-- regroups, and closes with the induction hypothesis.
--
-- geom n + 2ℚ * recipPow2 n ≡ 2ℚ。基例是 0 + 2 * 1 ≡ 2；步例用 two-mul
-- 把新项换成旧项的两倍、重排、再用归纳假设收口。
geom-closed : (n : ℕ) → geom n + 2ℚ * recipPow2 n ≡ 2ℚ
geom-closed zero = begin
  0ℚ + 2ℚ * recipPow2 0  ≡⟨ cong (λ z → 0ℚ + 2ℚ * z) recipPow2-0 ⟩
  0ℚ + 2ℚ * 1ℚ           ≡⟨ cong (0ℚ +_) (*-identityʳ 2ℚ) ⟩
  0ℚ + 2ℚ                ≡⟨ +-identityˡ 2ℚ ⟩
  2ℚ                     ∎
geom-closed (suc n) = begin
  geom (suc n) + 2ℚ * recipPow2 (suc n)
    ≡⟨ cong (λ z → (geom n + recipPow2 n) + 2ℚ * z) (recipPow2-suc n) ⟩
  (geom n + recipPow2 n) + 2ℚ * (recipPow2 n * half)
    ≡⟨ cong (λ z → (geom n + recipPow2 n) + z) (two-mul (recipPow2 n)) ⟩
  (geom n + recipPow2 n) + recipPow2 n
    ≡⟨ +-assoc (geom n) (recipPow2 n) (recipPow2 n) ⟩
  geom n + (recipPow2 n + recipPow2 n)
    ≡⟨ cong (geom n +_) (sym (two-mul-add (recipPow2 n))) ⟩
  geom n + 2ℚ * recipPow2 n
    ≡⟨ geom-closed n ⟩
  2ℚ  ∎

------------------------------------------------------------------------
-- Scaling a shifted geometric sum
--
-- 平移后的几何和按倍缩放

-- geom (n + d) ≡ geom n + recipPow2 n * geom d: the tail of a geometric
-- sum is the startup term times a fresh geometric sum. This is the form
-- every tail estimate uses, since it turns "sum of a decaying tail" into
-- "one factor times a bounded mass".
--
-- geom (n + d) ≡ geom n + recipPow2 n * geom d：几何和的尾部等于首项乘以
-- 一个全新的几何和。这是所有尾估计使用的形态，因为它把"衰减尾部之和"
-- 变成"一个因子乘以一个有界质量"。
geom-shift : (n d : ℕ) → geom (n +ℕ d) ≡ geom n + recipPow2 n * geom d
geom-shift n zero = begin
  geom (n +ℕ zero)             ≡⟨ cong geom (+-identityʳ n) ⟩
  geom n                       ≡⟨ sym (ℚP.+-identityʳ (geom n)) ⟩
  geom n + 0ℚ                  ≡⟨ cong (geom n +_) (sym (*-zeroʳ (recipPow2 n))) ⟩
  geom n + recipPow2 n * 0ℚ    ∎
geom-shift n (suc d) = begin
  geom (n +ℕ suc d)
    ≡⟨ cong geom (+-suc n d) ⟩
  geom (n +ℕ d) + recipPow2 (n +ℕ d)
    ≡⟨ cong₂ _+_ (geom-shift n d) (recipPow2-mul n d) ⟩
  (geom n + recipPow2 n * geom d) + (recipPow2 n * recipPow2 d)
    ≡⟨ +-assoc (geom n) (recipPow2 n * geom d) (recipPow2 n * recipPow2 d) ⟩
  geom n + (recipPow2 n * geom d + recipPow2 n * recipPow2 d)
    ≡⟨ cong (geom n +_) (sym (*-distribˡ-+ (recipPow2 n) (geom d) (recipPow2 d))) ⟩
  geom n + recipPow2 n * (geom d + recipPow2 d)
    ≡⟨ refl ⟩
  geom n + recipPow2 n * geom (suc d)
    ∎

------------------------------------------------------------------------
-- Order level: the geometric mass is at most two
--
-- 序层：几何质量不超过二

-- Everything above is equality; this block is the only place where the
-- ℚ order enters. The pattern is the same as everywhere else in this
-- repository: instead of subtracting to reach 0 ≤ 2 - geom n, add on the
-- non-negative remainder and then rewrite with the closed form.
-- 0ℚ ≤ 2ℚ, from Real's 0≤embed at 1: 2ℚ is embed 2.
--
-- 上面全是等式；这一段是 ℚ 序唯一进入的地方。手法与全仓一致：不做减法
-- 去凑 0 ≤ 2 - geom n，而是把非负的余项加上去、再用闭式改写。
-- 0ℚ ≤ 2ℚ，取自 Real 的 0≤embed 在 1 处：2ℚ 就是 embed 2。
0≤2ℚ : 0ℚ ≤ 2ℚ
0≤2ℚ = 0≤embed 2

-- The doubled halvings are non-negative.
--
-- 加倍后的折半非负。
two-nonNeg : (n : ℕ) → 0ℚ ≤ 2ℚ * recipPow2 n
two-nonNeg n =
  ≤-trans (subst (λ z → 0ℚ ≤ z) (sym (*-zeroʳ 2ℚ)) (≤-refl {0ℚ}))
    (*-mono-≤-nonNeg {a = 2ℚ} {a' = 2ℚ} {b = 0ℚ} {b' = recipPow2 n}
      0≤2ℚ ≤-refl (≤-refl {0ℚ}) (0≤recipPow2 n))

-- The geometric mass itself is non-negative.
--
-- 几何质量本身非负。
geom-nonNeg : (n : ℕ) → 0ℚ ≤ geom n
geom-nonNeg zero    = ≤-refl
geom-nonNeg (suc n) = +-mono-≤ (geom-nonNeg n) (0≤recipPow2 n)

-- p ≤ p + q when q is non-negative, with the right identity absorbed.
--
-- q 非负时 p ≤ p + q，顺带把右单位吸收掉。
le-self-add : {p q : ℚ} → 0ℚ ≤ q → p ≤ p + q
le-self-add {p} {q} 0≤q =
  subst (λ z → z ≤ p + q) (ℚP.+-identityʳ p) (+-monoʳ-≤ p 0≤q)

-- The geometric mass is at most two, straight from geom-closed.
--
-- 几何质量不超过二，直接来自 geom-closed。
geom-le : (n : ℕ) → geom n ≤ 2ℚ
geom-le n =
  subst (λ z → geom n ≤ z) (geom-closed n) (le-self-add (two-nonNeg n))

-- Scaling by a halving preserves the bound.
--
-- 用一次折半作乘子仍保持该界。
geom-scaled-le : (n d : ℕ) → recipPow2 n * geom d ≤ 2ℚ * recipPow2 n
geom-scaled-le n d =
  subst (λ z → recipPow2 n * geom d ≤ z) (*-comm (recipPow2 n) 2ℚ)
    (*-mono-≤-nonNeg {a = recipPow2 n} {a' = recipPow2 n} {b = geom d} {b' = 2ℚ}
      (0≤recipPow2 n) ≤-refl (geom-nonNeg d) (geom-le d))

-- The suffix bound: any later geometric mass, added to the prefix, stays
-- below prefix plus twice the startup halving. This is the estimate
-- series convergence is built on.
--
-- 后缀界：任意更长的几何质量加到前缀后，仍不超过前缀加首项折半的两倍。
-- 级数收敛就架在这条估计上。
geom-suffix-le : (n d : ℕ) → geom (n +ℕ d) ≤ geom n + 2ℚ * recipPow2 n
geom-suffix-le n d =
  subst (λ z → z ≤ geom n + 2ℚ * recipPow2 n) (sym (geom-shift n d))
    (+-monoʳ-≤ (geom n) (geom-scaled-le n d))

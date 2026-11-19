------------------------------------------------------------------------
-- Order facts for atan on [0,1]
--
-- [0,1] 上反正切的序性质
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Atan.Order where

open import Real.Interval.Mul.Order using (l-0)

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; <⇒≤; +-identityˡ
  ; +-mono-≤; neg-antimono-<; <-asym)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Real.CauchyToInterval using (M; centre-cauchy→realI)
open import Real.IntervalEquiv using (l; u; centre; centre-l; centre-u)
open import Real.Interval using (embedℚ; δ; δ-pos)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Atan.Core using
  (atanTerm; atanTerm-zero; atanTerm-nonNeg; atanTerm-dec; altSum; altSum-bounds
  ; atanSeq; atanq)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.OrderLe using (≤ℝ-antisym)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- Endpoints of the rational embedding
--
-- 有理嵌入的端点

-- atanq is built by cauchy→realI from partial sums that all sit in
-- [0, q]. The order on RealI is the negative of the strict order
-- (x ≤ℝ y means y <ℝ x is impossible), so each bound below is proved by
-- refuting the opposite strict inequality: a witness level n yields
--   u(atanq) n < l(0ℝ) n = -δ n        (for non-negativity),
--   u(embedℚ r) n = δ n + r < l(atanq) n   (for the upper bound),
-- and the centre identity centre (atanq) n ≡ altSum (atanTerm q) (M n)
-- together with 0 ≤ altSum ≤ q turns each into "0 < -δ n" or "r < r",
-- which the antisymmetry of _<_ refutes. The two-sided bound on the
-- partial sums is the AltInfo projection already proved in Core, and
-- the endpoint values of embedℚ are recovered from node-dyadic.
-- atanq-nonNeg, atanq≤q, atanq≤1 and atanq-zero form the slice. The
-- strict form 0ℝ <ℝ atanq q for 0 < q is not here: it needs a positive
-- lower bound for the partial sums, which AltInfo does not provide.
-- Both follow from node-dyadic at start level 0. They are local because
-- 0ℝ/1ℝ are used only here; a real embedding module would be the home
-- for them once a second caller appears.
--
-- atanq 由 cauchy→realI 从全部落在 [0, q] 内的部分和构造。RealI 上的序是
-- 严格序的否定（x ≤ℝ y 意为 y <ℝ x 不可能），故下面每条界都通过反驳相反
-- 的严格不等式来证：一个见证层级 n 给出
--   u(atanq) n < l(0ℝ) n = -δ n        （非负性），
--   u(embedℚ r) n = δ n + r < l(atanq) n   （上界），
-- 再借中心恒等式 centre (atanq) n ≡ altSum (atanTerm q) (M n) 与
-- 0 ≤ altSum ≤ q 化为 "0 < -δ n" 或 "r < r"，由 _<_ 的反对称性反驳。
-- 部分和的双边界就是 Core 已证的 AltInfo 投影，embedℚ 的端点值由
-- node-dyadic 还原。
-- 本切片为 atanq-nonNeg、atanq≤q、atanq≤1、atanq-zero。0 < q 时的严格
-- 形式 0ℝ <ℝ atanq q 不在此列：它需要部分和的正下界，而 AltInfo 不提供。
-- 两条都由起点 0 的 node-dyadic 得到；Node 模块已把同一事实整理成
-- l-dyadic / u-dyadic，这里直接复用。
l-embedℚ : (q : ℚ) (n : ℕ) → l (embedℚ q) n ≡ neg (δ n) + q
l-embedℚ q n = l-dyadic q n

u-embedℚ : (q : ℚ) (n : ℕ) → u (embedℚ q) n ≡ δ n + q
u-embedℚ q n = u-dyadic q n

------------------------------------------------------------------------
-- Bounds on the partial sums
--
-- 部分和的界

altSum-zero : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (d : ℕ)
            → 0ℚ ≤ altSum (atanTerm q) d
altSum-zero q 0≤q q≤1 d =
  proj₁ (altSum-bounds (atanTerm q) (atanTerm-dec q 0≤q q≤1)
           (atanTerm-nonNeg q 0≤q) d)

altSum-le-q : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (d : ℕ)
            → altSum (atanTerm q) d ≤ q
altSum-le-q q 0≤q q≤1 d =
  ≤-trans (proj₂ (altSum-bounds (atanTerm q) (atanTerm-dec q 0≤q q≤1)
                  (atanTerm-nonNeg q 0≤q) d))
          (≤-reflexive (atanTerm-zero q))

------------------------------------------------------------------------
-- Non-negativity
--
-- 非负性

atanq-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ)
             → 0ℝ ≤ℝ atanq q 0≤q q≤1
atanq-nonNeg q 0≤q q≤1 (n , h) =
  let
    h' : u (atanq q 0≤q q≤1) n < neg (δ n)
    h' = subst (λ z → u (atanq q 0≤q q≤1) n < z) (l-0 n) h
    u≥0 : 0ℚ ≤ u (atanq q 0≤q q≤1) n
    u≥0 = ≤-trans
            (subst (λ z → 0ℚ ≤ z)
                   (sym (centre-cauchy→realI (atanSeq q 0≤q q≤1) n))
                   (altSum-zero q 0≤q q≤1 (M (atanSeq q 0≤q q≤1) n)))
            (centre-u (atanq q 0≤q q≤1) n)
    pos : 0ℚ < neg (δ n)
    pos = ≤-<-trans u≥0 h'
  in <-asym pos (neg-antimono-< (δ-pos n))

------------------------------------------------------------------------
-- Upper bounds
--
-- 上界

-- One proof for every rational r above q, so that both "atanq ≤ q" and
-- "atanq ≤ 1" are instances, and "atanq ≈ 0" reuses the q = 0 case.
--
-- 对任意 q 以上的有理数 r 统一证明一次，于是 "atanq ≤ q" 与 "atanq ≤ 1"
-- 都是实例，"atanq ≈ 0" 复用 q = 0 的情形。
atanq-le-r : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ) (r : ℚ) (q≤r : q ≤ r)
           → atanq q 0≤q q≤1 ≤ℝ embedℚ r
atanq-le-r q 0≤q q≤1 r q≤r (n , h) =
  let
    h' : δ n + r < l (atanq q 0≤q q≤1) n
    h' = subst (λ z → z < l (atanq q 0≤q q≤1) n) (u-embedℚ r n) h
    c≤q : centre (atanq q 0≤q q≤1) n ≤ q
    c≤q = subst (λ z → z ≤ q)
            (sym (centre-cauchy→realI (atanSeq q 0≤q q≤1) n))
            (altSum-le-q q 0≤q q≤1 (M (atanSeq q 0≤q q≤1) n))
    c≤r : centre (atanq q 0≤q q≤1) n ≤ r
    c≤r = ≤-trans c≤q q≤r
    l≤r : l (atanq q 0≤q q≤1) n ≤ r
    l≤r = ≤-trans (centre-l (atanq q 0≤q q≤1) n) c≤r
    lt : δ n + r < r
    lt = <-≤-trans h' l≤r
    r≤ : r ≤ δ n + r
    r≤ = subst (λ z → z ≤ δ n + r) (+-identityˡ r)
           (+-mono-≤ (<⇒≤ (δ-pos n)) (≤-refl {r}))
    rr : r < r
    rr = ≤-<-trans r≤ lt
  in <-asym rr rr

atanq≤q : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ)
        → atanq q 0≤q q≤1 ≤ℝ embedℚ q
atanq≤q q 0≤q q≤1 = atanq-le-r q 0≤q q≤1 q (≤-refl {q})

atanq≤1 : (q : ℚ) (0≤q : 0ℚ ≤ q) (q≤1 : q ≤ 1ℚ)
        → atanq q 0≤q q≤1 ≤ℝ 1ℝ
atanq≤1 q 0≤q q≤1 = atanq-le-r q 0≤q q≤1 1ℚ q≤1

------------------------------------------------------------------------
-- Vanishing at zero
--
-- 在零处消失

-- Antisymmetry turns the two bounds at q = 0 into an approximate
-- equality with the rational zero, without unfolding the series at all.
--
-- 反对称性把 q = 0 处的两条界合成为与有理零的近似相等，完全不用展开级数。
atanq-zero : (0≤0 : 0ℚ ≤ 0ℚ) (0≤1 : 0ℚ ≤ 1ℚ)
           → atanq 0ℚ 0≤0 0≤1 ≈ℝ 0ℝ
atanq-zero 0≤0 0≤1 =
  ≤ℝ-antisym (atanq-le-r 0ℚ 0≤0 0≤1 0ℚ (≤-refl {0ℚ}))
             (atanq-nonNeg 0ℚ 0≤0 0≤1)

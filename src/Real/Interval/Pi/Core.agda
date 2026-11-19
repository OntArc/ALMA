------------------------------------------------------------------------
-- pi as four times atan 1, with the strict lower bound 3 < pi
--
-- π 定义为 4 atan 1，并给出严格下界 3 < π
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Pi.Core where

open import Data.Nat using (ℕ; suc; _∸_) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using
  (≤-trans; m+[n∸m]≡n; +-suc; m≤m+n; +-identityˡ)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; _*_; _/_)
open import Data.Rational.Properties using
  (≤-refl; <-≤-trans; +-assoc; +-comm; *-identityˡ; <ᵇ⇒<)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Base.RationalRing using (0≤1; lt-shift)
open import Real using (CauchySeq)
open import Real.CauchyToInterval using (M; μ≤M; K; node-go)
open import Real.IntervalEquiv using (l; u)
open import Real.Interval using (RealI; embedℚ; δ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Atan.Core using
  (atanTerm; atanTerm-dec; atanTerm-nonNeg; sign; altSum; shift; altSum-bounds
  ; atanSeq; atanq)
open import Real.Interval.Continuity using (0<embedℚ)
open import Real.Interval.Equiv using (≈ℝ-sym)
open import Real.Interval.Embed using (embedℚ-*)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using (*ℝ-comm)
open import Real.Interval.Mul.Order using (<-*mono; ≈-<-respʳ)
open import Real.Interval.Node using (u-dyadic-k)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.Series.Bounds using (le-self-add)

------------------------------------------------------------------------
-- The sequence and its partial sums
--
-- 序列与部分和

atanPartial : ℕ → ℚ
atanPartial d = altSum (atanTerm 1ℚ) d

term1 : ℕ → ℚ
term1 n = atanTerm 1ℚ n

one-le-one : 1ℚ ≤ 1ℚ
one-le-one = ≤-refl

atan1 : RealI
atan1 = atanq 1ℚ 0≤1 one-le-one

sample : CauchySeq
sample = atanSeq 1ℚ 0≤1 one-le-one

------------------------------------------------------------------------
-- From the even index 8 on, the partial sums never decrease
--
-- 从偶数下标 8 起，部分和不会下降

-- At the even index 8 the alternating sign is +1, so the remaining tail is
-- a non-negative alternating sum and no parity induction over all d ≥ 8 is
-- needed.
--
-- 偶数下标 8 处交错符号为 +1，故余下尾项是非负交错和，不必对一切 d ≥ 8
-- 做奇偶归纳。
sign-8 : sign 8 ≡ 1ℚ
sign-8 = refl

tail-dec : (j : ℕ) → term1 (8 +ℕ suc j) ≤ term1 (8 +ℕ j)
tail-dec j =
  subst (λ z → term1 z ≤ term1 (8 +ℕ j)) (sym (+-suc 8 j))
    (atanTerm-dec 1ℚ 0≤1 one-le-one (8 +ℕ j))

tail-nonNeg : (d : ℕ) → 0ℚ ≤ altSum (λ j → term1 (8 +ℕ j)) d
tail-nonNeg d =
  proj₁ (altSum-bounds (λ j → term1 (8 +ℕ j)) tail-dec
          (λ j → atanTerm-nonNeg 1ℚ 0≤1 (8 +ℕ j)) d)

shift-8 : (d : ℕ) →
  atanPartial (8 +ℕ d) ≡ atanPartial 8 + altSum (λ j → term1 (8 +ℕ j)) d
shift-8 d =
  trans (shift (atanTerm 1ℚ) 8 d)
    (cong (_+_ (atanPartial 8))
      (trans (cong (_* altSum (λ j → term1 (8 +ℕ j)) d) sign-8)
             (*-identityˡ (altSum (λ j → term1 (8 +ℕ j)) d))))

partial-mono-from-8 : (d : ℕ) → atanPartial 8 ≤ atanPartial (8 +ℕ d)
partial-mono-from-8 d =
  subst (λ z → atanPartial 8 ≤ z) (sym (shift-8 d))
    (le-self-add {p = atanPartial 8}
                  {q = altSum (λ j → term1 (8 +ℕ j)) d} (tail-nonNeg d))

partial-mono : (D' : ℕ) → 8 ≤ℕ D' → atanPartial 8 ≤ atanPartial D'
partial-mono D' 8≤D' =
  subst (λ z → atanPartial 8 ≤ atanPartial z)
    (m+[n∸m]≡n {8} {D'} 8≤D') (partial-mono-from-8 (D' ∸ 8))

------------------------------------------------------------------------
-- The closed bound 3/4 + 2 (δ 9) < atanPartial 8
--
-- 闭值界 3/4 + 2 (δ 9) < atanPartial 8

closed-bound : ℚ
closed-bound = (+ 3 / 4) + (δ 9 + δ 9)

closed-bound<8 : closed-bound < atanPartial 8
closed-bound<8 = <ᵇ⇒< tt

------------------------------------------------------------------------
-- The sample index is at least 8
--
-- 采样下标至少为 8

K-9 : K 9 ≡ 2048
K-9 = refl

2049≤sample : 2049 ≤ℕ M sample 9
2049≤sample =
  subst (λ z → suc z ≤ℕ M sample 9) (sym K-9) (μ≤M sample 9)

8≤sample : 8 ≤ℕ M sample 9
8≤sample = ≤-trans (m≤m+n 8 2041) 2049≤sample

------------------------------------------------------------------------
-- The rational statement
--
-- 有理层面的陈述

reassoc : closed-bound ≡ δ 9 + (δ 9 + (+ 3 / 4))
reassoc =
  trans (+-comm (+ 3 / 4) (δ 9 + δ 9))
    (sym (+-assoc (δ 9) (δ 9) (+ 3 / 4)))

-- The last step cancels one summand with lt-shift from Base.RationalRing
-- after commuting it into the position that lemma expects; it is not
-- re-proved here.
--
-- 最后一步先把加项换到 Base.RationalRing 的 lt-shift 所要求的位置，再用该
-- 引理消去一个加项；不在此处重证。
rational-bound : δ 9 + (+ 3 / 4) < atanPartial (M sample 9) - δ 9
rational-bound =
  let
    h : closed-bound < atanPartial (M sample 9)
    h = <-≤-trans closed-bound<8 (partial-mono (M sample 9) 8≤sample)
    h' : δ 9 + (δ 9 + (+ 3 / 4)) < atanPartial (M sample 9)
    h' = subst (λ z → z < atanPartial (M sample 9)) reassoc h
    h'' : (δ 9 + (+ 3 / 4)) + δ 9 < atanPartial (M sample 9)
    h'' = subst (λ z → z < atanPartial (M sample 9))
           (+-comm (δ 9) (δ 9 + (+ 3 / 4))) h'
  in lt-shift (δ 9 + (+ 3 / 4)) (atanPartial (M sample 9)) (δ 9) h''

------------------------------------------------------------------------
-- Endpoints of the two intervals
--
-- 两个区间的端点

l-atan : (n : ℕ) → l atan1 n ≡ atanPartial (M sample n) - δ n
l-atan n = trans (cong RealI.l (node-go sample n)) refl

-- No type signature on purpose: the inferred type names the index in exactly
-- the same syntactic form as rational-bound, and restating it would make Agda
-- compare two spellings of the sum. Two different spellings at M sample 9
-- unfold altSum at 2049 and ran over eleven minutes before failing on memory,
-- while the present form checks in about eight seconds.
--
-- 故意不写类型签名：推断出的类型与 rational-bound 中的下标语法形式完全一致，
-- 重写类型会迫使 Agda 比较该和的两种写法。两种写法在 M sample 9 处会展开
-- 2049 项 altSum，实测跑十一分钟以上后内存失败，而当前写法约八秒通过。
l-atan-9 = l-atan 9

-- Upper endpoint of an embedded rational, reused from Node, where the same
-- fact is already exported as u-dyadic-k.
--
-- 嵌入有理数的上端点，直接复用 Node 中已导出的 u-dyadic-k。
u-embed : u (embedℚ (+ 3 / 4)) 9 ≡ δ 9 + (+ 3 / 4)
u-embed =
  trans (u-dyadic-k (+ 3 / 4) 0 9)
    (cong (λ z → z + (+ 3 / 4)) (cong δ (+-identityˡ 9)))

three-quarters<atan1 : embedℚ (+ 3 / 4) <ℝ atan1
three-quarters<atan1 =
  let
    h : u (embedℚ (+ 3 / 4)) 9 < l atan1 9
    h = subst (λ z → z < l atan1 9) u-embed
          (subst (λ z → δ 9 + (+ 3 / 4) < z) (sym l-atan-9)
            rational-bound)
  in 9 , h

------------------------------------------------------------------------
-- pi and the lower bound 3 < pi
--
-- π 与下界 3 < π

-- pi = embedℚ 4 *ℝ atanq 1ℚ. The bound is read off level 9 of the interval
-- sequence cauchy→realI (atanSeq 1ℚ), whose left endpoint
-- altSum (atanTerm 1ℚ) (M X 9) - δ 9 already exceeds 3/4; multiplying the
-- strict bound 3/4 < atanq 1ℚ by the positive embedℚ 4 then gives 3 < pi.
--
-- π 定义为 4 atan 1。下界取自区间序列 cauchy→realI (atanSeq 1ℚ) 的第 9 层：
-- 其左端点 altSum (atanTerm 1ℚ) (M X 9) − δ 9 已超过 3/4；再把严格界
-- 3/4 < atanq 1ℚ 乘以正的 embedℚ 4，即得 3 < π。
pi : RealI
pi = embedℚ (+ 4 / 1) *ℝ atan1

four-positive : 0ℝ <ℝ embedℚ (+ 4 / 1)
four-positive = 0<embedℚ (+ 4 / 1) (<ᵇ⇒< tt)

scaled : embedℚ (+ 3 / 4) *ℝ embedℚ (+ 4 / 1)
       <ℝ atan1 *ℝ embedℚ (+ 4 / 1)
scaled = <-*mono (embedℚ (+ 3 / 4)) atan1 (embedℚ (+ 4 / 1))
           three-quarters<atan1 four-positive

three-quarters-times-four : (+ 3 / 4) * (+ 4 / 1) ≡ (+ 3 / 1)
three-quarters-times-four = refl

left-endpoint : embedℚ ((+ 3 / 4) * (+ 4 / 1)) <ℝ atan1 *ℝ embedℚ (+ 4 / 1)
left-endpoint =
  ≈-<-resp (≈ℝ-sym (embedℚ-* (+ 3 / 4) (+ 4 / 1))) scaled

three-quarters<pi : embedℚ (+ 3 / 1) <ℝ atan1 *ℝ embedℚ (+ 4 / 1)
three-quarters<pi =
  subst (λ q → embedℚ q <ℝ atan1 *ℝ embedℚ (+ 4 / 1))
    three-quarters-times-four left-endpoint

3ℝ : RealI
3ℝ = embedℚ (+ 3 / 1)

-- 3 < pi. Still missing at this layer: strict positivity 0ℝ <ℝ atanq q for
-- 0 < q (needs a positive lower bound on the partial sums, which AltInfo does
-- not provide), the upper bound pi <ℝ 4 (needs non-strict multiplication
-- monotonicity), and bounds such as pi <ℝ 22/7.
--
-- 3 < π。本层尚未给出：0 < q 时 0ℝ <ℝ atanq q 的严格正性（需要部分和的
-- 正下界，AltInfo 不提供）；上界 π <ℝ 4（需要非严格乘法单调律）；以及
-- π <ℝ 22/7 一类界。
three<pi : 3ℝ <ℝ pi
three<pi = ≈-<-respʳ (*ℝ-comm atan1 (embedℚ (+ 4 / 1))) three-quarters<pi

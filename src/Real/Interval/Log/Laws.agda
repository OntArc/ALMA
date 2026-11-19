------------------------------------------------------------------------
-- Laws of the logarithm
--
-- 对数的基本律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Log.Laws where

open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; _<_; _≤_)
open import Data.Rational.Properties using (≤-refl; ≤-trans; <⇒≤)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Equiv using (≈ℝ-sym; ≈ℝ-refl)
open import Real.Interval.Exp.Core using (expq)
open import Real.Interval.Exp.Order using (expq-zero)
import Real.Interval.Log.Core as LogC
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using
  (≤ℝ-refl; <-≤ℝ-trans; ≤ℝ-<trans; ≤ℝ-resp-≈)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)

------------------------------------------------------------------------
-- The cut, the supremum and its two rules, at a fixed base
--
-- 固定底数下的割、上确界及其两条规则

module _ (y : RealI) (1<y : 1ℝ <ℝ y) where

  -- For a base y with 1 < y, the logarithm of Log.Core is the supremum of
  -- the cut of rational points whose exponential is still below y. This
  -- module records the elementary laws of that supremum:
  --   log-nonNeg       0 ≤ log y
  --   log-of-member    embedℚ q ≤ log y   whenever expq q < y
  --   log-le-rat       log y ≤ embedℚ q   whenever y ≤ expq q
  --   log-mono         log is monotone in the base
  --   log-expq-upper   log (expq q) ≤ embedℚ q for q > 0
  -- Not yet included: the reverse of the last law,
  --   embedℚ q ≤ log (expq q),
  -- whose density-based proof drives the type checker into a conversion
  -- blow-up (measured on this machine: over five minutes at 1.15 GB with
  -- no progress, the same shape that previously killed the memory budget
  -- of the expq linear-growth slice). It is left to a dedicated slice that
  -- avoids abstracting terms whose type mentions the supremum.
  --   log-nonNeg       0 ≤ log y
  --
  -- 对满足 1 < y 的底数 y，Log.Core 的对数是"指数仍在 y 以下的有理点"
  -- 之割的上确界。本模块记录该上确界的基本律：
  --   log-of-member    当 expq q < y 时 embedℚ q ≤ log y
  --   log-le-rat       当 y ≤ expq q 时 log y ≤ embedℚ q
  --   log-mono         log 对底数单调
  --   log-expq-upper   对 q > 0 有 log (expq q) ≤ embedℚ q
  -- 尚未包含上一条的逆，即
  --   embedℚ q ≤ log (expq q)，
  -- 其基于稠密性的证明会让类型检查进入转换爆炸（本机实测：五分钟以上、
  -- 1.15 GB 且无进展；与此前拖垮 expq 线性增长片内存预算的形态同源）。
  -- 留待一个避免抽象"类型提及上确界"的项的专门切片。
  P : RealI → Set
  P = LogC.P y 1<y

  P-0 : P (embedℚ 0ℚ)
  P-0 = LogC.P-0 y 1<y

  logℝ : RealI
  logℝ = LogC.logℝ y 1<y

  log-upper : (x : RealI) → P x → x ≤ℝ logℝ
  log-upper = LogC.log-upper y 1<y

  log-least : (u₀ : RealI) → ((x : RealI) → P x → x ≤ℝ u₀) → logℝ ≤ℝ u₀
  log-least = LogC.log-least y 1<y

  log-member : (q : ℚ) (0≤q : 0ℚ ≤ q) → expq q 0≤q <ℝ y → P (embedℚ q)
  log-member = LogC.log-member y 1<y

  ----------------------------------------------------------------------
  -- Non-negativity
  --
  -- 非负性

  log-nonNeg : 0ℝ ≤ℝ logℝ
  log-nonNeg = log-upper 0ℝ P-0

  ----------------------------------------------------------------------
  -- The two bounds
  --
  -- 双侧界

  -- Rational points whose exponential is below y lie below the logarithm.
  --
  -- 指数低于 y 的有理点位于对数之下。
  log-of-member : (q : ℚ) (0≤q : 0ℚ ≤ q) → expq q 0≤q <ℝ y
                → embedℚ q ≤ℝ logℝ
  log-of-member q 0≤q q<y = log-upper (embedℚ q) (log-member q 0≤q q<y)

  -- If y is already below expq q, then q bounds the logarithm from above.
  --
  -- 若 y 已低于 expq q，则 q 从上方界住对数。
  log-le-rat : (q : ℚ) (0≤q : 0ℚ ≤ q) → y ≤ℝ expq q 0≤q
             → logℝ ≤ℝ embedℚ q
  log-le-rat q 0≤q y≤eq = log-least (embedℚ q) aux
    where
    aux : (x : RealI) → P x → x ≤ℝ embedℚ q
    aux x (r , (0≤r , (x≈ , er<y))) h =
      let
        -- q < r, since otherwise expq q ≤ expq r < y ≤ expq q.
        --
        -- 必有 q < r：否则 expq q ≤ expq r < y ≤ expq q。
        eq<r : embedℚ q <ℝ embedℚ r
        eq<r = ≈-<-respʳ x≈ h

        q<r : q < r
        q<r = embedℚ-reflect q r eq<r

        0≤r' : 0ℚ ≤ r
        0≤r' = ≤-trans 0≤q (<⇒≤ q<r)

        mono : expq q 0≤q ≤ℝ expq r 0≤r'
        mono = LogC.expq-mono-any q r 0≤q 0≤r' (<⇒≤ q<r)

        -- The member stores its own proof of 0 ≤ r; move the inequality
        -- to the proof used by the monotonicity lemma.
        --
        -- 成员存储的是它自己的 0 ≤ r 证明，把不等式搬到单调性引理所用
        -- 的证明项上。
        er<y' : expq r 0≤r' <ℝ y
        er<y' = ≈-<-resp (LogC.expq-irrel r 0≤r 0≤r') er<y

        eq<y : expq q 0≤q <ℝ y
        eq<y = ≤ℝ-<trans mono er<y'
      in
        y≤eq eq<y

  ----------------------------------------------------------------------
  -- Monotonicity in the base
  --
  -- 对底数的单调性

  log-mono : (x : RealI) (1<x : 1ℝ <ℝ x) → x ≤ℝ y
           → LogC.logℝ x 1<x ≤ℝ logℝ
  log-mono x 1<x x≤y = LogC.log-least x 1<x logℝ aux
    where
    aux : (z : RealI) → LogC.P x 1<x z → z ≤ℝ logℝ
    aux z (r , (0≤r , (z≈ , er<x))) =
      ≤ℝ-resp-≈ (≈ℝ-sym z≈) ≈ℝ-refl
        (log-upper (embedℚ r)
          (log-member r 0≤r (<-≤ℝ-trans er<x x≤y)))

------------------------------------------------------------------------
-- The upper half of the round trip log ∘ expq at rational points
--
-- 有理点上 log ∘ expq 往返律的上半

-- The non-negativity proof used for expq below; it is written so that it
-- coincides definitionally with the proof that expq-strict-mono produces.
--
-- 下文 expq 所用的非负性证明：其写法与 expq-strict-mono 产生的证明项
-- 定义相等。
0≤q-of : (q : ℚ) → 0ℚ < q → 0ℚ ≤ q
0≤q-of q 0<q = ≤-trans (≤-refl {0ℚ}) (<⇒≤ 0<q)

-- expq q exceeds 1 as soon as q > 0, since expq 0 ≈ 1 and expq is strict.
--
-- 只要 q > 0 就有 expq q 超过 1：expq 0 ≈ 1 且 expq 严格单调。
1<expq-of : (q : ℚ) (0<q : 0ℚ < q) → 1ℝ <ℝ expq q (0≤q-of q 0<q)
1<expq-of q 0<q =
  ≈-<-resp expq-zero
    (LogC.expq-strict-any 0ℚ q (≤-refl {0ℚ}) (0≤q-of q 0<q) 0<q)

-- Since expq q is itself the base, log (expq q) ≤ q is the rule
-- log-le-rat read at the boundary y ≤ expq q, which holds by reflexivity.
-- Note the shape of the term below: the boundary instantiation must be
-- written inline. Wrapping the two proofs in a where block instead makes
-- the checker expand the whole supremum machinery (measured: over five
-- minutes at 1.15 GB without finishing), while the inlined form checks
-- in about nine seconds.
--
-- 由于 expq q 自身就是底数，log (expq q) ≤ q 就是把 log-le-rat 读在
-- 边界 y ≤ expq q 上，而该边界由自反性给出。
-- 注意下项的写法：边界实例化必须内联。若把两个证明放进 where 块，
-- 检查器会展开整个上确界机制（实测：五分钟以上、1.15 GB 仍未完成），
-- 而内联写法约九秒通过。
log-expq-upper : (q : ℚ) (0<q : 0ℚ < q)
               → LogC.logℝ (expq q (0≤q-of q 0<q)) (1<expq-of q 0<q)
                 ≤ℝ embedℚ q
log-expq-upper q 0<q =
  log-le-rat (expq q (0≤q-of q 0<q)) (1<expq-of q 0<q)
    q (0≤q-of q 0<q) ≤ℝ-refl

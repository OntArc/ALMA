------------------------------------------------------------------------
-- The round trip log (exp q) = q on the rational line
--
-- 有理直线上的往返律 log (exp q) = q
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Log.RoundTrip where

open import Data.Product using (_,_)
open import Data.Rational using (ℚ; _<_; _≤_)
open import Data.Rational.Properties using (<-cmp)
open import Relation.Nullary using (¬_)

open import Real.Interval using (embedℚ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-pos; expq-total-mono; expq-total-strict-mono)
open import Real.Interval.Log.Full as LogF using (P; logℝ-total)
open import Real.Interval.Order using (_<ℝ_; <-irrefl)
open import Real.Interval.OrderComplete.Base using (Subset; _≤ℝ_)
open import Real.Interval.OrderComplete.Limit using (sup-≤-of-limit)
open import Real.Interval.OrderLe using
  (≤ℝ-antisym; ≤ℝ-resp-≈; ≤ℝ-<trans; <⇒≤ℝ)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)

------------------------------------------------------------------------
-- The two halves
--
-- 上下两半

-- The base is the total exponential at the variable point q, so nothing in
-- this module ever compares two exponentials at concrete points
--   upper  log (exp q) ≤ q : every member r satisfies exp r < exp q, hence
--          r < q, because q ≤ r would put exp q ≤ exp r by monotonicity
--   lower  q ≤ log (exp q) : below q the cut is dense, by density of the
--          rationals together with strict monotonicity at the variable
--          point s < q
-- The two halves meet in ≤ℝ-antisym. Neither half unfolds the supremum
-- while building its proof: the limit argument is the generic lemma
-- SupBelow.≤-of-limit, applied once here.
--
-- 底数是变量点 q 处的全指数，故本模块从不比较两个具体点上的指数
--   upper  log (exp q) ≤ q：每个成员 r 都有 exp r < exp q，于是 r < q，
--          因为 q ≤ r 会由单调性给出 exp q ≤ exp r
--   lower  q ≤ log (exp q)：q 之下割是稠密的，依据是有理数的稠密性
--          连同变量点 s < q 处的严格单调性
-- 两半由 ≤ℝ-antisym 合拢。两半在造证明时都不展开上确界：极限那一步用的是
-- 一般性引理 SupBelow.≤-of-limit，在这里应用一次。
module _ (q : ℚ) where

  P-cut : Subset
  P-cut = LogF.P (expq-total q) (expq-total-pos q)

  log-expq-total-upper :
      LogF.logℝ-total (expq-total q) (expq-total-pos q) ≤ℝ embedℚ q
  log-expq-total-upper =
    LogF.log-total-least (expq-total q) (expq-total-pos q) (embedℚ q)
      (λ x (r , (x≈ , er<q)) →
        let
          nle : ¬ (q ≤ r)
          nle q≤r = <-irrefl (expq-total q)
                      (≤ℝ-<trans (expq-total-mono q r q≤r) er<q)

          r<q : r < q
          r<q = LogF.not-le-strict r q (<-cmp r q) nle

          er<eq : embedℚ r <ℝ embedℚ q
          er<eq = embedℚ-mono r q r<q
        in
          ≤ℝ-resp-≈ (≈ℝ-sym x≈) ≈ℝ-refl (<⇒≤ℝ er<eq))

  log-expq-total-lower :
      embedℚ q ≤ℝ LogF.logℝ-total (expq-total q) (expq-total-pos q)
  log-expq-total-lower =
    sup-≤-of-limit {P = P-cut}
      (LogF.located (expq-total q) (expq-total-pos q))
      {x₀ = LogF.x₀ (expq-total q) (expq-total-pos q)}
      (LogF.x₀-member (expq-total q) (expq-total-pos q))
      {u₀ = embedℚ (LogF.M (expq-total q) (expq-total-pos q))}
      (LogF.isUpper (expq-total q) (expq-total-pos q))
      q
      (λ x x<eq →
        let
          s , (x<es , es<eq) = dense {x = x} {y = embedℚ q} x<eq

          s<q : s < q
          s<q = embedℚ-reflect s q es<eq

          es<eq : expq-total s <ℝ expq-total q
          es<eq = expq-total-strict-mono s q s<q
        in
          embedℚ s , ((s , (≈ℝ-refl , es<eq)) , x<es))

  log-expq-total :
      LogF.logℝ-total (expq-total q) (expq-total-pos q) ≈ℝ embedℚ q
  log-expq-total =
    ≤ℝ-antisym log-expq-total-upper log-expq-total-lower

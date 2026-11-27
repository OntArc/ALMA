------------------------------------------------------------------------
-- Quantitative brackets for expq
--
-- expq 的定量括号
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Bracket where

open import Data.Nat using (ℕ)
open import Data.Nat.Properties as NatP using (≤-total)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_)
open import Data.Rational.Properties using (≤-trans; <⇒≤)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Real.Interval using (embedℚ)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Exp.Core using
  (expPartial; expq; exp-bracket-le; expPartial-le; _≤ℕ_)
open import Real.Interval.Exp.PartialLe using (expPartial-le-expq)
open import Real.Interval.Exp.UpperBound using (expq-le-of-partials)

------------------------------------------------------------------------
-- Case elimination at a constant result type
--
-- 常结果类型的和消去

-- `Data.Sum.Base.[_,_]` is the dependent eliminator, so its type family
-- has to be supplied by the caller; at a constant result type the two
-- branches determine it, which is what this helper exposes.
--
-- Data.Sum.Base.[_,_] 是依赖消去子，其类型族须由调用方给出；结果类型为常数
-- 时两分支即可确定它，本辅助函数把这个形状单独取出。
sum-const : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
sum-const f g (inj₁ a) = f a
sum-const f g (inj₂ b) = g b

------------------------------------------------------------------------
-- The upper half at a prescribed index
--
-- 指定指标处的上半支

-- The same argument as in `expq-le-of-partials`, but the tail bound is
-- supplied by the caller instead of being computed from
-- `exp-bracket-le`. This matters for the crossing argument: the index
-- used by the bisection has to be the very index certified here, for the
-- same point.
--
-- 与 expq-le-of-partials 同法，只是尾界由调用方给出，而不是从
-- exp-bracket-le 算出来。这一点对跨越论证很关键：二分用的指标必须就是这里
-- 被认证的那个指标，并且针对同一个点。
expq-le-of-tail : (q : ℚ) (0≤q : 0ℚ ≤ q) (N : ℕ) (d : ℚ) (0<d : 0ℚ < d)
                → ((m : ℕ) → N ≤ℕ m → expPartial q m ≤ expPartial q N + d)
                → expq q 0≤q ≤ℝ embedℚ (expPartial q N + d)
expq-le-of-tail q 0≤q N d 0<d cert =
  let
    C : ℚ
    C = expPartial q N + d

    bound : (n : ℕ) → expPartial q n ≤ C
    bound n =
      sum-const (λ n≤N → ≤-trans (expPartial-le q 0≤q n N n≤N)
                    (le-self-add {p = expPartial q N} {q = d} (<⇒≤ 0<d)))
                (λ N≤n → cert n N≤n)
                (NatP.≤-total n N)
  in
    expq-le-of-partials q 0≤q C bound

------------------------------------------------------------------------
-- The bracket
--
-- 括号

expq-bracket : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
             → Σ ℕ (λ N → (embedℚ (expPartial q N) ≤ℝ expq q 0≤q)
                        × (expq q 0≤q ≤ℝ embedℚ (expPartial q N + d)))
expq-bracket q 0≤q d 0<d =
  let
    N , (low , high) = exp-bracket-le q 0≤q d 0<d

    lower : embedℚ (expPartial q N) ≤ℝ expq q 0≤q
    lower = expPartial-le-expq q 0≤q N
  in
    N , (lower , expq-le-of-tail q 0≤q N d 0<d high)

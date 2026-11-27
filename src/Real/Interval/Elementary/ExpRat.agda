------------------------------------------------------------------------
-- Partial sums at rational points
--
-- 有理点上的部分和
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.ExpRat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Exp.Core using (expPartial; expq)
open import Real.Interval.Exp.Order using (expPartial-two)
open import Real.Interval.Exp.PartialLe using (expPartial-le-expq)
open import Real.Interval.Exp.AboveLimit using (expq-above)
open import Real.Interval.Exp.Series using
  (expPartialℝ; expPartialℝ-≤-of-bound; expPartialℝ-≥-of-bound)
open import Real.Interval.Elementary.Exp using
  (Pℝ; Pℝ-member; Pℝ-zero; Pℝ-isUpper; located; expℝ; expℝ-upper; expℝ-least)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using (≤ℝ-refl; ≈⇒≤ℝ; ≤ℝ-antisym; <-≤ℝ-trans)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Limit using (sup-≤-of-limit)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤)

------------------------------------------------------------------------
-- The embedded rational is non-negative
--
-- 嵌入的有理点非负

-- `embedℚ 0ℚ` is `0ℝ` by definition, so monotonicity of the embedding
-- transfers `0 ≤ q` to the reals.
--
-- 定义上 embedℚ 0ℚ 就是 0ℝ，故嵌入的单调性把 0 ≤ q 搬到实数层。
embed-nonNeg : (q : ℚ) → 0ℚ ≤ q → 0ℝ ≤ℝ embedℚ q
embed-nonNeg q 0≤q = embedℚ-≤ 0ℚ q 0≤q

------------------------------------------------------------------------
-- The clamp collapses at a rational point
--
-- 有理点上的夹逼退化

-- With x = embedℚ q and m = M = q the two-sided clamp reads
--   embedℚ (expPartial q n) ≤ expPartialℝ (embedℚ q) n
--                            ≤ embedℚ (expPartial q n),
-- and antisymmetry turns it into an equality.
--
-- 取 x = embedℚ q、m = M = q，双边夹成为
--   即 embedℚ (expPartial q n) ≤ expPartialℝ (embedℚ q) n
--     且 ≤ embedℚ (expPartial q n)，
-- 由反对称性即得相等。
expPartialℝ-at-rat : (q : ℚ) (0≤q : 0ℚ ≤ q) (n : ℕ)
                   → expPartialℝ (embedℚ q) n ≈ℝ embedℚ (expPartial q n)
expPartialℝ-at-rat q 0≤q n =
  let
    x : RealI
    x = embedℚ q

    0≤x : 0ℝ ≤ℝ x
    0≤x = embed-nonNeg q 0≤q

    x≤x : x ≤ℝ x
    x≤x = ≤ℝ-refl

    upper : expPartialℝ x n ≤ℝ embedℚ (expPartial q n)
    upper = expPartialℝ-≤-of-bound x q 0≤x x≤x 0≤q n

    lower : embedℚ (expPartial q n) ≤ℝ expPartialℝ x n
    lower = expPartialℝ-≥-of-bound x q 0≤q x≤x n
  in
    ≤ℝ-antisym upper lower

------------------------------------------------------------------------
-- Two terms at a rational point
--
-- 有理点上的前两项

-- The second partial sum is exactly `1 + q`.
--
-- 第二个部分和恰为 1 + q。
expPartialℝ-embed-two : (q : ℚ) (0≤q : 0ℚ ≤ q)
                      → expPartialℝ (embedℚ q) (suc (suc zero))
                        ≈ℝ embedℚ (1ℚ + q)
expPartialℝ-embed-two q 0≤q =
  ≈ℝ-trans (expPartialℝ-at-rat q 0≤q (suc (suc zero)))
    (subst (λ z → z ≈ℝ embedℚ (1ℚ + q))
      (sym (cong embedℚ (expPartial-two q)))
      ≈ℝ-refl)

------------------------------------------------------------------------
-- The cut at a rational point is above `1 + q`
--
-- 有理点处的割在 1 + q 之上

-- `embedℚ (1 + q)` is a member at index two, so the cut dominates it.
--
-- embedℚ (1 + q) 在下标二是成员，故割在其上。
expℝ-ge-two : (q : ℚ) (0≤q : 0ℚ ≤ q)
            → embedℚ (1ℚ + q) ≤ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expℝ-ge-two q 0≤q =
  let
    x : RealI
    x = embedℚ q

    0≤x : 0ℝ ≤ℝ x
    0≤x = embed-nonNeg q 0≤q

    member : Pℝ x 0≤x (embedℚ (1ℚ + q))
    member = Pℝ-member x 0≤x (1ℚ + q)
      (suc (suc zero) , ≈⇒≤ℝ (≈ℝ-sym (expPartialℝ-embed-two q 0≤q)))
  in
    expℝ-upper x 0≤x (embedℚ (1ℚ + q)) member

------------------------------------------------------------------------
-- The cut at a rational point lies below `expq`
--
-- 有理点处的割在 expq 之下

-- Every member of the cut is an embedded rational `r` with
-- `embedℚ r ≤ expPartialℝ x n`, and the partial sums of the real series
-- agree with the rational ones at `x = embedℚ q`, which in turn stay
-- below `expq q`. The cut is the least upper bound of these members.
--
-- 割的每个成员都是嵌入有理点 r，且 embedℚ r ≤ expPartialℝ x n；实级数
-- 的部分和在 x = embedℚ q 处与有理部分和一致，后者又不超过 expq q
-- 割是这些成员的最小上界。
expℝ-at-rat-le : (q : ℚ) (0≤q : 0ℚ ≤ q)
               → expℝ (embedℚ q) (embed-nonNeg q 0≤q) ≤ℝ expq q 0≤q
expℝ-at-rat-le q 0≤q =
  let
    x : RealI
    x = embedℚ q

    0≤x : 0ℝ ≤ℝ x
    0≤x = embed-nonNeg q 0≤q

    le : (z : RealI) → Pℝ x 0≤x z → z ≤ℝ expq q 0≤q
    le z (r , (z≈r , (n , r≤part))) =
      let
        step₁ : embedℚ r ≤ℝ embedℚ (expPartial q n)
        step₁ = ≤ℝ-trans {x = embedℚ r} {y = expPartialℝ x n}
                  {z = embedℚ (expPartial q n)}
                  r≤part (≈⇒≤ℝ (expPartialℝ-at-rat q 0≤q n))

        step₂ : embedℚ (expPartial q n) ≤ℝ expq q 0≤q
        step₂ = expPartial-le-expq q 0≤q n

        total : embedℚ r ≤ℝ expq q 0≤q
        total = ≤ℝ-trans {x = embedℚ r} {y = embedℚ (expPartial q n)}
                  {z = expq q 0≤q} step₁ step₂
      in
        ≤ℝ-trans {x = z} {y = embedℚ r} {z = expq q 0≤q}
          (≈⇒≤ℝ z≈r) total
  in
    expℝ-least x 0≤x (expq q 0≤q) le

------------------------------------------------------------------------
-- The cut at a rational point lies above `expq`
--
-- 有理点处的割在 expq 之上

-- Suppose the cut were strictly below `expq q`. Density yields a
-- rational `p` in between. Every real `z < embedℚ p` is then exceeded by
-- a member: since `embedℚ p < expq q`, some sampled partial sum already
-- passes `p`, and that embedded partial sum is a member of the cut. The
-- limit lemma `sup-≤-of-limit` then puts `embedℚ p` below the cut, which
-- contradicts the gap.
--
-- 设割严格低于 expq q。稠密性给出夹在中间的有理点 p。任何 z < embedℚ p
-- 都被某个成员超过：因 embedℚ p < expq q，某个采样部分和已经越过 p，
-- 而该嵌入部分和正是割的成员。极限引理 sup-≤-of-limit 于是把
-- embedℚ p 置于割之下，与间隙矛盾。
expq-le-expℝ-at-rat : (q : ℚ) (0≤q : 0ℚ ≤ q)
                    → expq q 0≤q ≤ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expq-le-expℝ-at-rat q 0≤q lt =
  let
    x : RealI
    x = embedℚ q

    0≤x : 0ℝ ≤ℝ x
    0≤x = embed-nonNeg q 0≤q

    cut : RealI
    cut = expℝ x 0≤x

    p , (cut<p , p<expq) = dense {x = cut} {y = expq q 0≤q} lt

    hyp : (z : RealI) → z <ℝ embedℚ p
        → Σ RealI (λ y → Pℝ x 0≤x y × (z <ℝ y))
    hyp z z<p =
      let
        n , p≤part = expq-above q 0≤q p p<expq

        y : RealI
        y = embedℚ (expPartial q n)

        member : Pℝ x 0≤x y
        member = Pℝ-member x 0≤x (expPartial q n)
          (n , ≈⇒≤ℝ (≈ℝ-sym (expPartialℝ-at-rat q 0≤q n)))

        p≤y : embedℚ p ≤ℝ y
        p≤y = embedℚ-≤ p (expPartial q n) p≤part

        z<y : z <ℝ y
        z<y = <-≤ℝ-trans {x = z} {y = embedℚ p} {z = y} z<p p≤y
      in
        y , (member , z<y)
  in
    (sup-≤-of-limit {P = Pℝ x 0≤x} (located x 0≤x) (Pℝ-zero x 0≤x)
      (Pℝ-isUpper x 0≤x) p hyp) cut<p

------------------------------------------------------------------------
-- Identity at a rational point
--
-- 有理点处的同一性

expℝ-at-rat : (q : ℚ) (0≤q : 0ℚ ≤ q)
            → expℝ (embedℚ q) (embed-nonNeg q 0≤q) ≈ℝ expq q 0≤q
expℝ-at-rat q 0≤q =
  ≤ℝ-antisym (expℝ-at-rat-le q 0≤q) (expq-le-expℝ-at-rat q 0≤q)

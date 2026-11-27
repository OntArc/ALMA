------------------------------------------------------------------------
-- Order laws of the total logarithm
--
-- 全对数的序律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Log.Order where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _<_; _≤_)
open import Data.Rational.Properties using (<-cmp; ≤-refl; <-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import Base.RationalRing using (0<1)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono; 0<embedℚ)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Exp.Dense using (expq-dense; lt-split)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-mono; expq-total-nonNeg; expq-total-pos
  ; expq-total-le-one; expq-total-zero)
open import Real.Interval.Log.Full as LogF using
  (logℝ-total; log-total-upper; log-total-member; not-le-strict)
open import Real.Interval.Log.RoundTrip using (log-expq-total)
open import Real.Interval.Order using (_<ℝ_; <-irrefl)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.OrderLe using
  (≤ℝ-resp-≈; ≤ℝ-antisym; ≈⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans; <⇒≤ℝ)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)

------------------------------------------------------------------------
-- Monotonicity in the base
--
-- 对底数的单调性

-- Every member r of the cut at y reads expq-total r < y ≤ z, so it is a
-- member of the cut at z as well; log z is an upper bound of the cut at
-- y, and the least upper bound log y lies below it.
--
-- y 的割里每个成员 r 都读 expq-total r < y ≤ z，故它也是 z 的割的成员；
-- log z 是 y 的割的上界，而上确界 log y 在其下。
log-total-mono : (y z : RealI) (0<y : 0ℝ <ℝ y) (0<z : 0ℝ <ℝ z)
               → y ≤ℝ z
               → LogF.logℝ-total y 0<y ≤ℝ LogF.logℝ-total z 0<z
log-total-mono y z 0<y 0<z y≤z =
  LogF.log-total-least y 0<y (LogF.logℝ-total z 0<z)
    (λ x (r , (x≈ , er<y)) →
      ≤ℝ-resp-≈ (≈ℝ-sym x≈) ≈ℝ-refl
        (log-total-upper z 0<z (embedℚ r)
          (r , (≈ℝ-refl , <-≤ℝ-trans er<y y≤z))))

------------------------------------------------------------------------
-- A rational upper bound
--
-- 有理上界

-- If expq-total q already reaches y, then every member r of the cut at y
-- has expq-total r < expq-total q, so r < q by monotonicity, and q
-- bounds the logarithm from above.
--
-- 若 expq-total q 已到达 y，则 y 的割里每个成员 r 都有
-- expq-total r < expq-total q，由单调性得 r < q，于是 q 从上方界住对数。
log-total-le-rat : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                 → y ≤ℝ expq-total q
                 → LogF.logℝ-total y 0<y ≤ℝ embedℚ q
log-total-le-rat y 0<y q y≤eq =
  LogF.log-total-least y 0<y (embedℚ q)
    (λ x (r , (x≈ , er<y)) →
      let
        nle : ¬ (q ≤ r)
        nle q≤r =
          <-irrefl (expq-total q)
            (≤ℝ-<trans (expq-total-mono q r q≤r)
              (<-≤ℝ-trans er<y y≤eq))

        r<q : r < q
        r<q = not-le-strict r q (<-cmp r q) nle

        er<eq : embedℚ r <ℝ embedℚ q
        er<eq = embedℚ-mono r q r<q
      in
        ≤ℝ-resp-≈ (≈ℝ-sym x≈) ≈ℝ-refl (<⇒≤ℝ er<eq))

------------------------------------------------------------------------
-- Replacement in the base
--
-- 在底数上的替换律

-- Two equal bases have equal logarithms: monotonicity gives both
-- directions and antisymmetry closes them into equality.
--
-- 两个相等的底数有相等的对数：单调性给出两个方向，反对称性合成相等。
log-total-cong : (y z : RealI) (0<y : 0ℝ <ℝ y) (0<z : 0ℝ <ℝ z)
               → y ≈ℝ z
               → LogF.logℝ-total y 0<y ≈ℝ LogF.logℝ-total z 0<z
log-total-cong y z 0<y 0<z y≈z =
  ≤ℝ-antisym
    (log-total-mono y z 0<y 0<z (≈⇒≤ℝ y≈z))
    (log-total-mono z y 0<z 0<y (≈⇒≤ℝ (≈ℝ-sym y≈z)))

------------------------------------------------------------------------
-- Value laws
--
-- 取值律

log-total-one : LogF.logℝ-total 1ℝ 0ℝ<ℝ1ℝ ≈ℝ 0ℝ
log-total-one =
  ≈ℝ-trans
    (log-total-cong 1ℝ (expq-total 0ℚ) 0ℝ<ℝ1ℝ (expq-total-pos 0ℚ)
      (≈ℝ-sym expq-total-zero))
    (log-expq-total 0ℚ)

------------------------------------------------------------------------
-- Sign laws
--
-- 符号律

-- The logarithm is non-negative above 1 and non-positive below it.
--
-- 对数在 1 以上非负、在 1 以下非正。
log-total-nonNeg : (y : RealI) (0<y : 0ℝ <ℝ y) (1≤y : 1ℝ ≤ℝ y)
                 → 0ℝ ≤ℝ LogF.logℝ-total y 0<y
log-total-nonNeg y 0<y 1≤y =
  ≤ℝ-resp-≈ log-total-one ≈ℝ-refl
    (log-total-mono 1ℝ y 0ℝ<ℝ1ℝ 0<y 1≤y)

log-total-nonPos : (y : RealI) (0<y : 0ℝ <ℝ y) (y≤1 : y ≤ℝ 1ℝ)
                 → LogF.logℝ-total y 0<y ≤ℝ 0ℝ
log-total-nonPos y 0<y y≤1 =
  log-total-le-rat y 0<y 0ℚ
    (≤ℝ-resp-≈ ≈ℝ-refl (≈ℝ-sym expq-total-zero) y≤1)

------------------------------------------------------------------------
-- Strict positivity above one
--
-- 超过一时的严格正性

-- `expq-dense` squeezes the total exponential at a rational point `q`
-- strictly between `1` and a rational `r` that already lies below `y`
-- Since `expq-total 1` is `1`, the point `q` cannot satisfy `q ≤ 0`, where
-- `expq-total-le-one` would pull the exponential back to `1`; so `q` is
-- strictly positive, and being a member of the cut it stays strictly below
-- the logarithm.
--
-- `expq-dense` 把某有理点 `q` 处的总指数严格夹在 `1` 与已低于 `y` 的有理点
-- `r` 之间。`1` 处的总指数正是 `1`，故 `q` 不可能满足 `q ≤ 0`——那会由
-- `expq-total-le-one` 把指数拉回 `1`——于是 `q` 严格为正，而它作为割的成员
-- 又使对数严格在 `0` 之上。
log-total-pos : (y : RealI) (0<y : 0ℝ <ℝ y) (1<y : 1ℝ <ℝ y)
              → 0ℝ <ℝ LogF.logℝ-total y 0<y
log-total-pos y 0<y 1<y =
  let
    wr : Σ ℚ (λ r → (1ℝ <ℝ embedℚ r) × (embedℚ r <ℝ y))
    wr = dense 1<y

    r : ℚ
    r = proj₁ wr

    e1<er : 1ℝ <ℝ embedℚ r
    e1<er = proj₁ (proj₂ wr)

    er<y : embedℚ r <ℝ y
    er<y = proj₂ (proj₂ wr)

    1<r : 1ℚ < r
    1<r = embedℚ-reflect 1ℚ r e1<er

    winq : Σ ℚ (λ q → (embedℚ 1ℚ <ℝ expq-total q)
                   × (expq-total q <ℝ embedℚ r))
    winq = expq-dense 1ℚ r 0<1 1<r

    q : ℚ
    q = proj₁ winq

    e1<eq : embedℚ 1ℚ <ℝ expq-total q
    e1<eq = proj₁ (proj₂ winq)

    eq<er : expq-total q <ℝ embedℚ r
    eq<er = proj₂ (proj₂ winq)

    eq<y : expq-total q <ℝ y
    eq<y = <-≤ℝ-trans eq<er (<⇒≤ℝ er<y)

    contra : q ≤ 0ℚ → ⊥
    contra q≤0 = <-irrefl 1ℝ (<-≤ℝ-trans e1<eq (expq-total-le-one q q≤0))

    pos : (0ℚ < q) ⊎ (q ≤ 0ℚ) → 0ℚ < q
    pos = λ { (inj₁ 0<q) → 0<q
            ; (inj₂ q≤0) → ⊥-elim (contra q≤0) }

    0<q : 0ℚ < q
    0<q = pos (lt-split 0ℚ q (<-cmp 0ℚ q))

    em≤x : embedℚ q ≤ℝ LogF.logℝ-total y 0<y
    em≤x = log-total-member y 0<y q eq<y

    0<em : 0ℝ <ℝ embedℚ q
    0<em = 0<embedℚ q 0<q
  in
    <-≤ℝ-trans 0<em em≤x

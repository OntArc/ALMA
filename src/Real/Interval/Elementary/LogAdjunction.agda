------------------------------------------------------------------------
-- Adjunction between log and the rational exponential
--
-- log 与有理指数之间的伴随关系
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.LogAdjunction where

open import Data.Empty using (⊥-elim)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_)
open import Data.Rational.Properties using (<⇒≤; <-cmp)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (dense)
open import Real.Interval.Exp.Dense using (expq-dense; lt-split)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-mono; expq-total-strict-mono; expq-total-pos)
open import Real.Interval.Log.Full using
  (P; logℝ-total; log-total-least; log-total-member
  ; located; x₀; x₀-member; M; isUpper)
open import Real.Interval.OrderComplete using (sup-member-of-lt)
open import Real.Interval.Order using (_<ℝ_; <-trans)
open import Real.Interval.OrderLe using (≈⇒≤ℝ; <-≤ℝ-trans; ≤ℝ-<trans)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤; embedℚ-reflect)

------------------------------------------------------------------------
-- The rational exponential reflects strict order
--
-- 有理指数反射严格序

-- If `expq r < expq q` then `r < q`: the trichotomy leaves either `r < q`
-- directly, or `q ≤ r`, in which case monotonicity turns `expq q ≤ expq r`
-- into a refutation of the hypothesis.
--
-- 若 expq r < expq q 则 r < q：三分类要么直接给 r < q，要么给 q ≤ r，
-- 后者由单调性把 expq q ≤ expq r 变成对假设的反驳。
expq-total-reflect : (r q : ℚ) → expq-total r <ℝ expq-total q → r < q
expq-total-reflect r q h =
  let
    order : (r < q) ⊎ (q ≤ r)
    order = lt-split r q (<-cmp r q)
  in
    [ (λ r<q → r<q)
    , (λ q≤r → ⊥-elim (expq-total-mono q r q≤r h))
    ]′ order

------------------------------------------------------------------------
-- An exponential upper bound is a logarithm upper bound
--
-- 指数的上界是对数的上界

log-total-le-expq : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                  → y ≤ℝ expq-total q
                  → logℝ-total y 0<y ≤ℝ embedℚ q
log-total-le-expq y 0<y q y≤eq =
  log-total-least y 0<y (embedℚ q)
    (λ x (r , (x≈r , er<y)) →
      let
        er<eq : expq-total r <ℝ expq-total q
        er<eq = <-≤ℝ-trans {x = expq-total r} {y = y} {z = expq-total q}
                  er<y y≤eq

        r<q : r < q
        r<q = expq-total-reflect r q er<eq

        er≤eq : embedℚ r ≤ℝ embedℚ q
        er≤eq = embedℚ-≤ r q (<⇒≤ r<q)
      in
        ≤ℝ-trans {x = x} {y = embedℚ r} {z = embedℚ q}
          (≈⇒≤ℝ x≈r) er≤eq)

------------------------------------------------------------------------
-- The two sides of the adjunction
--
-- 伴随关系的两侧

-- Above the cut, the exponential dominates `y`: a point above the least
-- upper bound cannot itself have exponential below `y`, else it would be
-- a member and hence below the bound. Below the cut, the exponential
-- stays at most `y`: if `y` were strictly below `expq m`, every member `r`
-- would satisfy `expq r < expq m` and hence `r < m`, making `m` an upper
-- bound that beats the least one.
--
-- 在割之上，指数压住 y：上确界之上的点其指数不可能低于 y，否则它自己
-- 就是成员、从而低于上确界。在割之下，指数至多为 y：若 y 严格低于
-- expq m，则每个成员 r 都满足 expq r < expq m，故 r < m，于是 m 成为
-- 比最小上界还小的上界。
log-total-lt-expq : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                  → logℝ-total y 0<y <ℝ embedℚ q
                  → y ≤ℝ expq-total q
log-total-lt-expq y 0<y q log<q = λ q<y →
  (log-total-member y 0<y q q<y) log<q

expq-le-of-lt-log : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                  → embedℚ q <ℝ logℝ-total y 0<y
                  → expq-total q ≤ℝ y
expq-le-of-lt-log y 0<y q q<log = λ y<eq →
  let
    bound : (x : RealI) → P y 0<y x → x ≤ℝ embedℚ q
    bound x (r , (x≈r , er<y)) =
      let
        er<eq : expq-total r <ℝ expq-total q
        er<eq = <-trans er<y y<eq

        r<q : r < q
        r<q = expq-total-reflect r q er<eq

        er≤eq : embedℚ r ≤ℝ embedℚ q
        er≤eq = embedℚ-≤ r q (<⇒≤ r<q)
      in
        ≤ℝ-trans {x = x} {y = embedℚ r} {z = embedℚ q}
          (≈⇒≤ℝ x≈r) er≤eq

    le : logℝ-total y 0<y ≤ℝ embedℚ q
    le = log-total-least y 0<y (embedℚ q) bound
  in
    le q<log

------------------------------------------------------------------------
-- The two sides, read as questions about rational points
--
-- 两侧的等价说法：把有理点搬到割的两边

-- The adjunction above turns a comparison between the logarithm and a
-- rational point into one between the exponential at that point and `y`,
-- with a strict hypothesis on the first side. Both directions are
-- refutations, so each one also runs backwards: if the exponential at a
-- rational point stays strictly below `y`, that point cannot lie strictly
-- above the logarithm; if `y` stays strictly below the exponential, the
-- point cannot lie strictly below the logarithm. This is the shape the
-- case analysis on a window around `y` needs.
--
-- 上文的伴随关系把"对数与有理点的比较"换成"该点指数与 y 的比较"，且都把
-- 严格性放在第一侧。两个方向都是反驳，故都可反过来用：若某有理点的指数
-- 严格低于 y，则该点不可能严格高于对数；若 y 严格低于该点的指数，则该点
-- 不可能严格低于对数。这正是围绕 y 的窗口做情形分析时所需的形状。
log-le-rat-of-lt-expq : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                      → y <ℝ expq-total q
                      → logℝ-total y 0<y ≤ℝ embedℚ q
log-le-rat-of-lt-expq y 0<y q y<eq = λ q<log →
  (expq-le-of-lt-log y 0<y q q<log) y<eq

rat-le-log-of-expq-lt : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                      → expq-total q <ℝ y
                      → embedℚ q ≤ℝ logℝ-total y 0<y
rat-le-log-of-expq-lt y 0<y q eq<y = λ log<q →
  (log-total-lt-expq y 0<y q log<q) eq<y

------------------------------------------------------------------------
-- Strictly below the logarithm, the exponential stays strictly below y
--
-- 严格低于对数之处，指数严格低于 y

-- The cut of the logarithm holds every rational whose exponential stays
-- below `y`, and the logarithm is its least upper bound. A point strictly
-- below that bound therefore has a member above it
-- (`sup-member-of-lt`): a rational `r` with `exp r < y` and `q < r`
-- Strict monotonicity carries `exp q < exp r`, and the two comparisons
-- compose. Together with `log-total-lt-expq` this makes the logarithm
-- the exact interface between the two sides of `y` under the rational
-- exponential.
--
-- 对数的割含有每个指数低于 y 的有理点，而对数是它的最小上界。故严格低于该
-- 上界的点之上有成员（`sup-member-of-lt`）：存在有理 r 使 exp r < y 且 q < r
-- 严格单调性给出 exp q < exp r，两个比较于是接上。与 `log-total-lt-expq`
-- 合起来，对数恰是有理指数下 y 两侧之间的分界。
expq-lt-of-rat-lt-log : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                      → embedℚ q <ℝ logℝ-total y 0<y
                      → expq-total q <ℝ y
expq-lt-of-rat-lt-log y 0<y q q<log =
  let
    member : Σ RealI (λ x → P y 0<y x × (embedℚ q <ℝ x))
    member = sup-member-of-lt {P = P y 0<y} (located y 0<y)
               {x₀ = x₀ y 0<y} (x₀-member y 0<y)
               {u₀ = embedℚ (M y 0<y)} (isUpper y 0<y)
               (embedℚ q) q<log

    x : RealI
    x = proj₁ member

    px : P y 0<y x
    px = proj₁ (proj₂ member)

    qx : embedℚ q <ℝ x
    qx = proj₂ (proj₂ member)

    r : ℚ
    r = proj₁ px

    x≈r : x ≈ℝ embedℚ r
    x≈r = proj₁ (proj₂ px)

    er<y : expq-total r <ℝ y
    er<y = proj₂ (proj₂ px)

    q<r : q < r
    q<r = embedℚ-reflect q r (<-≤ℝ-trans qx (≈⇒≤ℝ x≈r))

    eq<er : expq-total q <ℝ expq-total r
    eq<er = expq-total-strict-mono q r q<r
  in
    <-trans eq<er er<y

------------------------------------------------------------------------
-- Above the logarithm, the exponential is strictly above y
--
-- 高于对数之处，指数严格高于 y

-- A rational point above the least upper bound already satisfies `y ≤ exp`
-- (`log-total-lt-expq`). Density inserts a rational point between the bound
-- and that point, and strict monotonicity of the rational exponential turns
-- the comparison inside the rationals into a strict one at the outer point
-- With the law below the cut this makes the logarithm the exact cut between
-- the rationals whose exponential stays below `y` and those whose
-- exponential exceeds it.
--
-- 高于最小上界的有理点已满足 y ≤ exp（`log-total-lt-expq`）。稠密性在上界与
-- 该点之间插入有理点，有理指数的严格单调性把有理点内部的那次比较变成外点处
-- 的严格比较。与割下那一条合起来，对数恰是指数低于 y 的有理点与指数超过 y
-- 的有理点之间的割。
expq-gt-of-log-lt-rat : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                      → logℝ-total y 0<y <ℝ embedℚ q
                      → y <ℝ expq-total q
expq-gt-of-log-lt-rat y 0<y q log<q =
  let
    win : Σ ℚ (λ q' → (logℝ-total y 0<y <ℝ embedℚ q')
                   × (embedℚ q' <ℝ embedℚ q))
    win = dense log<q

    q' : ℚ
    q' = proj₁ win

    log<eq' : logℝ-total y 0<y <ℝ embedℚ q'
    log<eq' = proj₁ (proj₂ win)

    eq'<eq : embedℚ q' <ℝ embedℚ q
    eq'<eq = proj₂ (proj₂ win)

    y≤eq' : y ≤ℝ expq-total q'
    y≤eq' = log-total-lt-expq y 0<y q' log<eq'

    q'<q : q' < q
    q'<q = embedℚ-reflect q' q eq'<eq

    eq'<eq' : expq-total q' <ℝ expq-total q
    eq'<eq' = expq-total-strict-mono q' q q'<q
  in
    ≤ℝ-<trans y≤eq' eq'<eq'

------------------------------------------------------------------------
-- Strictly above a point of the cut, the logarithm stays strictly above
--
-- 割成员之上，对数严格高于该点

-- `rat-le-log-of-expq-lt` gives only `embed q ≤ log y` when the exponential
-- at `q` stays below `y`. For a strict comparison one needs a member of the
-- cut strictly above `q`. Density first puts a rational `m` between
-- `expq q` and `y`, then a second one `r` between `embed m` and `y`, and
-- `expq-dense` produces `q'` whose exponential lies between `embed m` and
-- `embed r`. That makes `q'` a member of the cut, and `expq-total-reflect`
-- turns `expq q < expq q'` into `q < q'`, while `log-total-member` puts
-- `q'` below the logarithm. Strict monotonicity of the embedding closes the
-- chain.
--
-- 当 `q` 处的指数低于 `y` 时，`rat-le-log-of-expq-lt` 只给出
-- `embed q ≤ log y`。要严格的比较，需要在割中找到一个严格高于 `q` 的成员
-- 稠密性先把有理数 `m` 放在 `expq q` 与 `y` 之间，再把另一个有理数 `r` 放在
-- `embed m` 与 `y` 之间，`expq-dense` 于是产出指数落在 `embed m` 与
-- `embed r` 之间的 `q'`。这样 `q'` 是割的成员，`expq-total-reflect` 把
-- `expq q < expq q'` 反射成 `q < q'`，而 `log-total-member` 把 `q'` 压在对数
-- 之下。嵌入的严格单调性收束整条链。
rat-lt-log-of-expq-lt : (y : RealI) (0<y : 0ℝ <ℝ y) (q : ℚ)
                      → expq-total q <ℝ y
                      → embedℚ q <ℝ logℝ-total y 0<y
rat-lt-log-of-expq-lt y 0<y q eq<y =
  let
    w₁ : Σ ℚ (λ m → (expq-total q <ℝ embedℚ m) × (embedℚ m <ℝ y))
    w₁ = dense eq<y

    m : ℚ
    m = proj₁ w₁

    eq<m : expq-total q <ℝ embedℚ m
    eq<m = proj₁ (proj₂ w₁)

    m<y : embedℚ m <ℝ y
    m<y = proj₂ (proj₂ w₁)

    w₂ : Σ ℚ (λ r → (embedℚ m <ℝ embedℚ r) × (embedℚ r <ℝ y))
    w₂ = dense m<y

    r : ℚ
    r = proj₁ w₂

    m<rE : embedℚ m <ℝ embedℚ r
    m<rE = proj₁ (proj₂ w₂)

    r<y : embedℚ r <ℝ y
    r<y = proj₂ (proj₂ w₂)

    0<m : 0ℚ < m
    0<m = embedℚ-reflect 0ℚ m (<-trans (expq-total-pos q) eq<m)

    m<r : m < r
    m<r = embedℚ-reflect m r m<rE

    w₃ : Σ ℚ (λ q' → (embedℚ m <ℝ expq-total q')
                     × (expq-total q' <ℝ embedℚ r))
    w₃ = expq-dense m r 0<m m<r

    q' : ℚ
    q' = proj₁ w₃

    m<eq' : embedℚ m <ℝ expq-total q'
    m<eq' = proj₁ (proj₂ w₃)

    eq'<rE : expq-total q' <ℝ embedℚ r
    eq'<rE = proj₂ (proj₂ w₃)

    q<q' : q < q'
    q<q' = expq-total-reflect q q' (<-trans eq<m m<eq')

    eq<eq' : embedℚ q <ℝ embedℚ q'
    eq<eq' = embedℚ-mono q q' q<q'

    eq'≤log : embedℚ q' ≤ℝ logℝ-total y 0<y
    eq'≤log = log-total-member y 0<y q' (<-trans eq'<rE r<y)
  in
    <-≤ℝ-trans eq<eq' eq'≤log

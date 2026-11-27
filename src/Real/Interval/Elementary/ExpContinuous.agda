------------------------------------------------------------------------
-- Quantitative tools for the exponential modulus
--
-- 指数模数的定量工具
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Elementary.ExpContinuous where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _-_; Positive; positive)
open import Data.Sum.Base using ([_,_]′)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-<-trans; <⇒≤; +-mono-≤; *-identityʳ; *-distribˡ-+
  ; +-assoc; +-comm; +-identityˡ; <-trans; ≤-total; +-monoˡ-<; positive⁻¹)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; subst; cong; trans)

open import Base.RationalRing using (0≤1; 0<1)
open import Real using (ε; 0<ε; half)
open import Real.Archimedean using (le-add-right; rat-shrink; ε-≤-1)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_; negℝ)
open import Real.Interval.ArithLaws using
  (+ℝ-inverseʳ; +ℝ-identityˡ; +ℝ-identityʳ; +ℝ-comm; sub-add-cancelℝ)
open import Real.Interval.Continuity using
  (Close; close-mono; embedℚ-mono; 0<embedℚ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.Interval.Embed using (embedℚ-cong; embedℚ-+)
open import Real.Interval.Elementary.Exp using (expℝ)
open import Real.Interval.Elementary.ExpLaws using (expℝ-close-window)
open import Real.Interval.Elementary.Continuous using
  (rat-above; rat-window; rat-below-of-pos; sub-emb-pos; radius-refine)
open import Real.Interval.Exp.Core using (expPartial; expPartial-zero)
open import Real.Interval.Exp.Lipschitz using (expPartial-bound)
open import Real.Interval.Exp.Order using (expPartial-le-param)
open import Real.Interval.Kit using (*-mono-≤-nonNeg)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (<⇒≤ℝ; ≤ℝ-<trans; <-≤ℝ-trans; <-+mono-reflect; ≤ℝ-resp-≈; ≤ℝ-+-monoˡ)
open import Real.Interval.OrderLaws using (<-+mono; ≈-<-resp)
open import Real.Interval.Order using (_<ℝ_) renaming (<-trans to <-transR)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect; embedℚ-≤)

------------------------------------------------------------------------
-- Lifting a rational bound to a smaller rational point
--
-- 把有理界抬到更小的有理点

-- Partial sums are monotone in the rational argument, so a bound taken
-- at `U` also bounds every nonnegative point below `U`.
--
-- 部分和对有理变元单调，故在 `U` 处取的界也界住 `U` 之下的一切非负点。
expPartial-bound-below :
  (r U : ℚ) (0≤r : 0ℚ ≤ r) (r≤U : r ≤ U) (B : ℚ)
  (bndU : (j : ℕ) → expPartial U j ≤ B)
  → (j : ℕ) → expPartial r j ≤ B
expPartial-bound-below r U 0≤r r≤U B bndU j =
  ≤-trans (expPartial-le-param r U 0≤r r≤U j) (bndU j)

------------------------------------------------------------------------
-- A positive difference from a strict comparison
--
-- 由严格比较得到正差

-- Adding `neg x` on both sides of `x < y` turns `x` into `0` and `y`
-- into the difference, which is the definitional unfolding of `_-ℝ_`.
--
-- 在 `x < y` 两边加 `neg x`，把 `x` 变成 `0`、把 `y` 变成差，这正是
-- `_-ℝ_` 的定义展开。
sub-pos-of-lt : (x y : RealI) → x <ℝ y → 0ℝ <ℝ y -ℝ x
sub-pos-of-lt x y x<y =
  ≈-<-resp (+ℝ-inverseʳ x) (<-+mono x y (negℝ x) x<y)

------------------------------------------------------------------------
-- The squeeze radius against a single precision
--
-- 把夹逼半径压进单个精度

-- The closed-window squeeze leaves the radius `h * (1 + B) + e`. Since
-- `h` and `e` are both bounded by the depth `h₀` of the budget, the sum
-- lies below `h₀ * ((1 + 1) + B)`, and the budget puts that below `ε k`.
--
-- 闭窗夹逼留下的半径是 `h * (1 + B) + e`。由于 `h` 与 `e` 都不超过预算
-- 所用的深度 `h₀`，其和低于 `h₀ * ((1 + 1) + B)`，而预算又把后者压到
-- `ε k` 之下。
exp-budget : (h h₀ e B : ℚ) (0≤h : 0ℚ ≤ h) (0≤B : 0ℚ ≤ B)
             (h≤h₀ : h ≤ h₀) (e≤h₀ : e ≤ h₀) (k : ℕ)
             (budget : h₀ * ((1ℚ + 1ℚ) + B) < ε k)
           → h * (1ℚ + B) + e < ε k
exp-budget h h₀ e B 0≤h 0≤B h≤h₀ e≤h₀ k budget =
  let
    B' : ℚ
    B' = 1ℚ + B

    0≤B' : 0ℚ ≤ B'
    0≤B' = ≤-trans 0≤1 (le-add-right 1ℚ B 0≤B)

    h-term : h * B' ≤ h₀ * B'
    h-term = *-mono-≤-nonNeg 0≤h h≤h₀ 0≤B' (≤-refl {B'})

    e-term : e ≤ h₀ * 1ℚ
    e-term = subst (λ z → e ≤ z) (sym (*-identityʳ h₀)) e≤h₀

    sum≤ : h * B' + e ≤ h₀ * B' + h₀ * 1ℚ
    sum≤ = +-mono-≤ h-term e-term

    shift : B' + 1ℚ ≡ (1ℚ + 1ℚ) + B
    shift = trans (+-assoc 1ℚ B 1ℚ)
              (trans (cong (1ℚ +_) (+-comm B 1ℚ)) (sym (+-assoc 1ℚ 1ℚ B)))

    reassoc : h₀ * B' + h₀ * 1ℚ ≡ h₀ * ((1ℚ + 1ℚ) + B)
    reassoc = trans (sym (*-distribˡ-+ h₀ B' 1ℚ)) (cong (h₀ *_) shift)

    lt : h * B' + e < ε k
    lt = ≤-<-trans (subst (λ z → h * B' + e ≤ z) reassoc sum≤) budget
  in
    lt

------------------------------------------------------------------------
-- Adding a non-positive increment
--
-- 加上非正增量

-- A non-positive increment keeps the sum below its addend: replace the
-- increment by zero and then drop the zero addend on the left.
--
-- 非正增量使和不超过被加项：先把增量换成零，再去掉左侧的零加数。
add-nonPos-le : (p h : ℚ) → p ≤ 0ℚ → p + h ≤ h
add-nonPos-le p h p≤0 =
  let
    mid : p + h ≤ 0ℚ + h
    mid = +-mono-≤ p≤0 (≤-refl {h})

    last : 0ℚ + h ≤ h
    last = subst (λ z → 0ℚ + h ≤ z) (+-identityˡ h) (≤-refl)
  in
    ≤-trans mid last

------------------------------------------------------------------------
-- The squeeze with zero as lower endpoint
--
-- 以零为下端点的夹逼

-- Near the left end of the domain the rational window around the point
-- may start below `0`, where the exponential has no value yet. Both
-- points and the window's upper endpoint are nonnegative in that case,
-- so `0` itself serves as lower endpoint; the only mismatch against the
-- two-sided squeeze is that its upper endpoint is written `0 + r` and
-- not `r`, which congruence of the embedding and of the partial sums
-- removes.
--
-- 在定义域的左端附近，点周围的有理窗可能起于 `0` 之下，那里指数还没有
-- 取值。此时两个点与窗的上端点都非负，故直接以 `0` 作下端点；与双边夹
-- 逼的唯一差异是其上端点写作 `0 + r` 而非 `r`，嵌入与部分和的同余即可
-- 消去这一点。
expℝ-close-zero : (r : ℚ) (0≤r : 0ℚ ≤ r) (B : ℚ)
                   (bnd : (j : ℕ) → expPartial r j ≤ B)
                   (e : ℚ) (0<e : 0ℚ < e)
                   (x y : RealI) (0≤x : 0ℝ ≤ℝ x) (0≤y : 0ℝ ≤ℝ y)
                   (xr : x ≤ℝ embedℚ r) (yr : y ≤ℝ embedℚ r)
                 → Close (r * (1ℚ + B) + e) (expℝ x 0≤x) (expℝ y 0≤y)
expℝ-close-zero r 0≤r B bnd e 0<e x y 0≤x 0≤y xr yr =
  let
    zero-shift : 0ℚ + r ≡ r
    zero-shift = +-identityˡ r

    emb-shift : embedℚ (0ℚ + r) ≈ℝ embedℚ r
    emb-shift = embedℚ-cong zero-shift

    xr' : x ≤ℝ embedℚ (0ℚ + r)
    xr' = ≤ℝ-resp-≈ (≈ℝ-refl {x}) (≈ℝ-sym emb-shift) xr

    yr' : y ≤ℝ embedℚ (0ℚ + r)
    yr' = ≤ℝ-resp-≈ (≈ℝ-refl {y}) (≈ℝ-sym emb-shift) yr

    bnd' : (j : ℕ) → expPartial (0ℚ + r) j ≤ B
    bnd' j = subst (λ z → expPartial z j ≤ B) (sym zero-shift) (bnd j)

    0≤0 : 0ℚ ≤ 0ℚ
    0≤0 = ≤-refl
  in
    expℝ-close-window 0ℚ r 0≤0 0≤r B bnd' e 0<e x y 0≤x 0≤y 0≤x xr' 0≤y yr'

------------------------------------------------------------------------
-- Continuity of the exponential on the nonnegative part of the line
--
-- 指数在实轴非负部分上的连续性

-- A fixed rational `U` above the whole neighbourhood supplies one bound
-- `B` for all partial sums there. The budget `rat-shrink` picks a depth
-- `h₀` with `ε h₀ * ((1 + 1) + B) < ε k`; that depth is the window width
-- itself, and since no precision exceeds `1` the window stays under `U`
-- The radius is cut further below the distances from the point to the
-- window's two ends, which places the neighbour inside the window; below
-- the point the window is replaced by the zero-based one.
--
-- 邻域上方的一个固定有理数 `U` 为那里所有部分和给出同一个界 `B`。预算
-- `rat-shrink` 选出深度 `h₀` 使 `ε h₀ * ((1 + 1) + B) < ε k`；该深度本身
-- 就是窗宽，而每层精度都不超过一，故窗留在 `U` 之下。半径再压到点与窗
-- 两端的距离之下，把邻点放进窗内；点的左侧改用零基窗。
expℝ-continuous-at : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (k : ℕ)
                   → Σ ℚ (λ d → (0ℚ < d) ×
                       ((y : RealI) (0≤y : 0ℝ ≤ℝ y)
                       → Close d x y → Close (ε k) (expℝ x 0≤x) (expℝ y 0≤y)))
expℝ-continuous-at x 0≤x k =
  let
    au : Σ ℚ (λ U → x +ℝ embedℚ 1ℚ <ℝ embedℚ U
                        × (embedℚ U <ℝ (x +ℝ embedℚ 1ℚ) +ℝ embedℚ 1ℚ))
    au = rat-above (x +ℝ embedℚ 1ℚ) 1ℚ 0<1

    U : ℚ
    U = proj₁ au

    x+1<U : x +ℝ embedℚ 1ℚ <ℝ embedℚ U
    x+1<U = proj₁ (proj₂ au)

    0<1ℝ : 0ℝ <ℝ embedℚ 1ℚ
    0<1ℝ = 0<embedℚ 1ℚ 0<1

    x<x+1 : x <ℝ x +ℝ embedℚ 1ℚ
    x<x+1 = ≈-<-resp (+ℝ-identityˡ x)
              (≈-<-respʳ (+ℝ-comm (embedℚ 1ℚ) x)
                (<-+mono 0ℝ (embedℚ 1ℚ) x 0<1ℝ))

    0<x+1 : 0ℝ <ℝ x +ℝ embedℚ 1ℚ
    0<x+1 = ≤ℝ-<trans 0≤x x<x+1

    0<U : 0ℚ < U
    0<U = embedℚ-reflect 0ℚ U (<-transR 0<x+1 x+1<U)

    0≤U : 0ℚ ≤ U
    0≤U = <⇒≤ 0<U

    ub : Σ ℚ (λ B → (j : ℕ) → expPartial U j ≤ B)
    ub = expPartial-bound U 0≤U 1ℚ 0<1

    B : ℚ
    B = proj₁ ub

    bndU : (j : ℕ) → expPartial U j ≤ B
    bndU = proj₂ ub

    0≤B : 0ℚ ≤ B
    0≤B = subst (λ z → z ≤ B) (expPartial-zero U) (bndU zero)

    c : ℚ
    c = (1ℚ + 1ℚ) + B

    0≤11 : 0ℚ ≤ 1ℚ + 1ℚ
    0≤11 = ≤-trans 0≤1 (le-add-right 1ℚ 1ℚ 0≤1)

    0≤c : 0ℚ ≤ c
    0≤c = ≤-trans 0≤11 (le-add-right (1ℚ + 1ℚ) B 0≤B)

    rsh : Σ ℕ (λ j' → ε j' * c < ε k)
    rsh = rat-shrink c 0≤c (ε k) (0<ε k)

    j : ℕ
    j = proj₁ rsh

    budget : ε j * c < ε k
    budget = proj₂ rsh

    h₀ : ℚ
    h₀ = ε j

    0<h₀ : 0ℚ < h₀
    0<h₀ = 0<ε j

    e : ℚ
    e = h₀

    0<e : 0ℚ < e
    0<e = 0<h₀

    e≤h₀ : e ≤ h₀
    e≤h₀ = ≤-refl

    h : ℚ
    h = h₀

    0<h : 0ℚ < h
    0<h = 0<h₀

    h≤h₀ : h ≤ h₀
    h≤h₀ = ≤-refl

    h≤1 : h ≤ 1ℚ
    h≤1 = ε-≤-1 j

    0≤h : 0ℚ ≤ h
    0≤h = <⇒≤ 0<h

    win : Σ ℚ (λ p → (x -ℝ embedℚ h <ℝ embedℚ p)
                         × (embedℚ p <ℝ x × x <ℝ embedℚ (p + h)))
    win = rat-window x h 0<h

    p : ℚ
    p = proj₁ win

    p<x : embedℚ p <ℝ x
    p<x = proj₁ (proj₂ (proj₂ win))

    x<p+h : x <ℝ embedℚ (p + h)
    x<p+h = proj₂ (proj₂ (proj₂ win))

    r : ℚ
    r = p + h

    0<r : 0ℚ < r
    0<r = embedℚ-reflect 0ℚ r (≤ℝ-<trans 0≤x x<p+h)

    0≤r : 0ℚ ≤ r
    0≤r = <⇒≤ 0<r

    r<x+1 : embedℚ r <ℝ x +ℝ embedℚ 1ℚ
    r<x+1 =
      ≈-<-resp (≈ℝ-sym (embedℚ-+ p h))
        (<-≤ℝ-trans (<-+mono (embedℚ p) x (embedℚ h) p<x)
          (≤ℝ-+-monoˡ {embedℚ h} {embedℚ 1ℚ} {x} (embedℚ-≤ h 1ℚ h≤1)))

    r<U : embedℚ r <ℝ embedℚ U
    r<U = <-transR r<x+1 x+1<U

    r≤U : r ≤ U
    r≤U = <⇒≤ (embedℚ-reflect r U r<U)

    bnd : (i : ℕ) → expPartial r i ≤ B
    bnd i = expPartial-bound-below r U 0≤r r≤U B bndU i

    r≤h : p ≤ 0ℚ → r ≤ h
    r≤h p≤0 = add-nonPos-le p h p≤0

    top-gap : 0ℝ <ℝ embedℚ r -ℝ x
    top-gap = sub-pos-of-lt x (embedℚ r) x<p+h

    bt : Σ ℚ (λ t → 0ℚ < t × embedℚ t <ℝ embedℚ r -ℝ x)
    bt = rat-below-of-pos (embedℚ r -ℝ x) top-gap

    δt : ℚ
    δt = proj₁ bt

    0<δt : 0ℚ < δt
    0<δt = proj₁ (proj₂ bt)

    δt<gap : embedℚ δt <ℝ embedℚ r -ℝ x
    δt<gap = proj₂ (proj₂ bt)

    bot-gap : 0ℝ <ℝ x -ℝ embedℚ p
    bot-gap = sub-emb-pos x p p<x

    bb : Σ ℚ (λ b → 0ℚ < b × embedℚ b <ℝ x -ℝ embedℚ p)
    bb = rat-below-of-pos (x -ℝ embedℚ p) bot-gap

    δb : ℚ
    δb = proj₁ bb

    0<δb : 0ℚ < δb
    0<δb = proj₁ (proj₂ bb)

    δb<gap : embedℚ δb <ℝ x -ℝ embedℚ p
    δb<gap = proj₂ (proj₂ bb)

    ref1 : Σ ℚ (λ z → 0ℚ < z × (z < h × z < δt))
    ref1 = radius-refine h δt 0<h 0<δt

    d₁ : ℚ
    d₁ = proj₁ ref1

    0<d₁ : 0ℚ < d₁
    0<d₁ = proj₁ (proj₂ ref1)

    d₁<δt : d₁ < δt
    d₁<δt = proj₂ (proj₂ (proj₂ ref1))

    ref2 : Σ ℚ (λ z → 0ℚ < z × (z < d₁ × z < δb))
    ref2 = radius-refine d₁ δb 0<d₁ 0<δb

    d : ℚ
    d = proj₁ ref2

    0<d : 0ℚ < d
    0<d = proj₁ (proj₂ ref2)

    d<d₁ : d < d₁
    d<d₁ = proj₁ (proj₂ (proj₂ ref2))

    d<δb : d < δb
    d<δb = proj₂ (proj₂ (proj₂ ref2))

    d<δt : d < δt
    d<δt = <-trans d<d₁ d₁<δt

    y<top : (y : RealI) → Close d x y → y <ℝ embedℚ r
    y<top y (lft , rgt) =
      let
        xt<r : x +ℝ embedℚ δt <ℝ embedℚ r
        xt<r = ≈-<-respʳ (sub-add-cancelℝ (embedℚ r) x)
                 (≈-<-resp (+ℝ-comm (embedℚ δt) x)
                   (<-+mono (embedℚ δt) (embedℚ r -ℝ x) x δt<gap))

        xd≤xt : x +ℝ embedℚ d ≤ℝ x +ℝ embedℚ δt
        xd≤xt = ≤ℝ-+-monoˡ {embedℚ d} {embedℚ δt} {x}
                   (<⇒≤ℝ (embedℚ-mono d δt d<δt))

        xd<r : x +ℝ embedℚ d <ℝ embedℚ r
        xd<r = ≤ℝ-<trans xd≤xt xt<r
      in
        <-transR rgt xd<r

    p<y : (y : RealI) → Close d x y → embedℚ p <ℝ y
    p<y y (lft , rgt) =
      let
        ed<gap : embedℚ d <ℝ x -ℝ embedℚ p
        ed<gap = <-transR (embedℚ-mono d δb d<δb) δb<gap

        low : embedℚ d +ℝ embedℚ p <ℝ x
        low = ≈-<-respʳ (sub-add-cancelℝ x (embedℚ p))
                (<-+mono (embedℚ d) (x -ℝ embedℚ p) (embedℚ p) ed<gap)

        low' : embedℚ p +ℝ embedℚ d <ℝ x
        low' = ≈-<-resp (+ℝ-comm (embedℚ d) (embedℚ p)) low

        hyp : embedℚ p +ℝ embedℚ d <ℝ (x -ℝ embedℚ d) +ℝ embedℚ d
        hyp = ≈-<-respʳ (≈ℝ-sym (sub-add-cancelℝ x (embedℚ d))) low'

        p<x-d : embedℚ p <ℝ x -ℝ embedℚ d
        p<x-d = <-+mono-reflect {x = x -ℝ embedℚ d} {y = embedℚ p} {z = embedℚ d} hyp
      in
        <-transR p<x-d lft

    at : (y : RealI) (0≤y : 0ℝ ≤ℝ y) → Close d x y
       → Close (ε k) (expℝ x 0≤x) (expℝ y 0≤y)
    at y 0≤y cl =
      let
        x≤r : x ≤ℝ embedℚ r
        x≤r = <⇒≤ℝ x<p+h

        y≤r : y ≤ℝ embedℚ r
        y≤r = <⇒≤ℝ (y<top y cl)

        case-low : p ≤ 0ℚ → Close (ε k) (expℝ x 0≤x) (expℝ y 0≤y)
        case-low p≤0 =
          close-mono (r * (1ℚ + B) + e) (ε k) (expℝ x 0≤x) (expℝ y 0≤y)
            (exp-budget r h₀ e B 0≤r 0≤B (≤-trans (r≤h p≤0) h≤h₀) e≤h₀ k budget)
            (expℝ-close-zero r 0≤r B bnd e 0<e x y 0≤x 0≤y x≤r y≤r)

        case-high : 0ℚ ≤ p → Close (ε k) (expℝ x 0≤x) (expℝ y 0≤y)
        case-high 0≤p =
          close-mono (h * (1ℚ + B) + e) (ε k) (expℝ x 0≤x) (expℝ y 0≤y)
            (exp-budget h h₀ e B 0≤h 0≤B h≤h₀ e≤h₀ k budget)
            (expℝ-close-window p h 0≤p 0≤h B bnd e 0<e x y 0≤x 0≤y
               (<⇒≤ℝ p<x) x≤r (<⇒≤ℝ (p<y y cl)) y≤r)
      in
        [ case-low , case-high ]′ (≤-total p 0ℚ)
  in
    d , (0<d , at)

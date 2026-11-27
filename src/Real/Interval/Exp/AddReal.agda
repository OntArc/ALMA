------------------------------------------------------------------------
-- The exponential addition law at real points
--
-- 实数点处的指数加法律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.AddReal where

open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; +-mono-≤; +-assoc; +-comm; *-assoc
  ; *-identityʳ; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst)

open import Base.RationalRing using (0<1)
open import Real using (embed; ε; 0<ε)
open import Real.Archimedean using (rat-shrink; ε-≤-1; le-add-right)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-comm; sub-add-cancelℝ; +ℝ-identityˡ)
open import Real.Interval.Continuity using (Close; 0<embedℚ)
open import Real.Interval.DensityArch using (dense; ≤ℝ-of-slack)
open import Real.Interval.Elementary.Exp using (expℝ)
open import Real.Interval.Elementary.ExpLaws using
  (expℝ-close-window; expℝ-mono; expℝ-nonNeg)
open import Real.Interval.Elementary.ExpRat using (embed-nonNeg)
open import Real.Interval.Embed using (embedℚ-+)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.Interval.Exp.Core using (expPartial; expPartial-zero)
open import Real.Interval.Exp.Lipschitz using
  (expPartial-bound; prod-nonNeg)
open import Real.Interval.Exp.Order using (expPartial-le-param)
open import Real.Interval.Exp.AddShift using
  (expℝ-add-shift-le; rat-window-nonNeg; 0≤shift)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Order using (*ℝ-≤-mono; ≈-<-respʳ)
open import Real.Interval.Mul.Laws using (*ℝ-comm)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (<⇒≤ℝ; ≤ℝ-resp-≈; ≤ℝ-+-mono; ≤ℝ-+-monoˡ; ≤ℝ-<trans)
open import Real.Interval.OrderLaws using (≈-<-resp; <-+mono)
open import Real.Interval.Rational using (+rearrange)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤; embedℚ-reflect)

------------------------------------------------------------------------
-- Rearranging window endpoints
--
-- 窗端点的重排

-- The second window shifts the left endpoint by its whole width.
--
-- 第二个窗把左端点平移它自己的整个宽度。
qshift : (a b h : ℚ) → 0ℚ ≤ h → (a + h) + b ≤ (a + b) + (h + h)
qshift a b h 0≤h =
  let
    grown : (a + b) + h ≤ (a + b) + (h + h)
    grown = ≤-trans
              (le-add-right ((a + b) + h) h 0≤h)
              (≤-reflexive (+-assoc (a + b) h h))
  in
    ≤-trans (≤-reflexive (+rearrange a h b)) grown

-- Two summed windows carry twice the single width.
--
-- 两个窗相加，宽度是单窗的两倍。
qdouble : (a b h : ℚ) → (a + h) + (b + h) ≡ (a + b) + (h + h)
qdouble a b h =
  trans (sym (+-assoc (a + h) b h))
    (trans (cong (λ z → z + h) (+rearrange a h b))
      (+-assoc (a + b) h h))

-- The pair window stays below the point where the partial sums are bounded.
--
-- 并窗落在部分和被界住的那个点之下。
qbelow : (a b h U V : ℚ) → h ≤ 1ℚ → a + 1ℚ ≤ U → b + 1ℚ ≤ V
       → (a + b) + (h + h) ≤ U + V
qbelow a b h U V h≤1 a≤U b≤V =
  ≤-trans (+-mono-≤ (≤-refl {a + b}) (+-mono-≤ h≤1 h≤1))
    (≤-trans (≤-reflexive (sym (qdouble a b 1ℚ))) (+-mono-≤ a≤U b≤V))

-- The doubled width expressed against the tolerance.
--
-- 双倍宽度换算成容差。
qbudget : (hh B : ℚ)
       → (hh + hh) * (1ℚ + B) + hh ≡ hh * (((1ℚ + 1ℚ) * (1ℚ + B)) + 1ℚ)
qbudget hh B =
  let
    twice : hh + hh ≡ hh * (1ℚ + 1ℚ)
    twice = trans (sym (cong₂ (λ u v → u + v) (*-identityʳ hh) (*-identityʳ hh)))
              (sym (*-distribˡ-+ hh 1ℚ 1ℚ))

    merged : (hh + hh) * (1ℚ + B) ≡ hh * ((1ℚ + 1ℚ) * (1ℚ + B))
    merged = trans (cong (λ z → z * (1ℚ + B)) twice)
               (*-assoc hh (1ℚ + 1ℚ) (1ℚ + B))

    summed : hh * ((1ℚ + 1ℚ) * (1ℚ + B)) + hh
           ≡ hh * (((1ℚ + 1ℚ) * (1ℚ + B)) + 1ℚ)
    summed = trans (cong (λ z → hh * ((1ℚ + 1ℚ) * (1ℚ + B)) + z)
                      (sym (*-identityʳ hh)))
               (sym (*-distribˡ-+ hh ((1ℚ + 1ℚ) * (1ℚ + B)) 1ℚ))
  in
    trans (cong (λ z → z + hh) merged) summed

-- A sum of embedded rationals is the embedded sum.
--
-- 嵌入有理数之和是嵌入的和。
sum-emb : (p q : ℚ) → embedℚ p +ℝ embedℚ q ≈ℝ embedℚ (p + q)
sum-emb p q = ≈ℝ-sym (embedℚ-+ p q)

------------------------------------------------------------------------
-- Sums and tolerances at the real level
--
-- 实数层的和与容差

-- Every real point lies strictly below itself plus one.
--
-- 每个实数点都严格位于它自身加一之下。
lt-self-plus-one : (z : RealI) → z <ℝ z +ℝ embedℚ 1ℚ
lt-self-plus-one z =
  ≈-<-respʳ (+ℝ-comm (embedℚ 1ℚ) z)
    (≈-<-resp (+ℝ-identityˡ z)
      (<-+mono 0ℝ (embedℚ 1ℚ) z (0<embedℚ 1ℚ 0<1)))

-- Two nonnegative reals have a nonnegative sum.
--
-- 两个非负实数之和非负。
0≤add : (a b : RealI) → 0ℝ ≤ℝ a → 0ℝ ≤ℝ b → 0ℝ ≤ℝ a +ℝ b
0≤add a b 0≤a 0≤b =
  ≤ℝ-resp-≈ (+ℝ-identityˡ 0ℝ) (≈ℝ-refl {a +ℝ b})
    (≤ℝ-trans (≤ℝ-+-mono 0≤a) (≤ℝ-+-monoˡ 0≤b))

-- A tolerance subtracted on one side reappears added on the other.
--
-- 一侧减去的容差在另一侧加回来。
lt-of-sub-lt : (a b : RealI) (d : ℚ)
             → a -ℝ embedℚ d <ℝ b → a <ℝ b +ℝ embedℚ d
lt-of-sub-lt a b d h =
  ≈-<-resp (sub-add-cancelℝ a (embedℚ d))
    (<-+mono (a -ℝ embedℚ d) b (embedℚ d) h)

-- The lower branch of closeness.
--
-- 邻近关系的下界支。
close-below : (d : ℚ) (A B : RealI) → Close d A B → A ≤ℝ B +ℝ embedℚ d
close-below d A B c = <⇒≤ℝ (lt-of-sub-lt A B d (proj₁ c))

------------------------------------------------------------------------
-- The lower half
--
-- 下界半支

expℝ-add-real-le :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (y : RealI) (0≤y : 0ℝ ≤ℝ y)
  → expℝ (x +ℝ y) (0≤add x y 0≤x 0≤y)
    ≤ℝ expℝ x 0≤x *ℝ expℝ y 0≤y
expℝ-add-real-le x 0≤x y 0≤y =
  ≤ℝ-of-slack (expℝ (x +ℝ y) (0≤add x y 0≤x 0≤y))
    (expℝ x 0≤x *ℝ expℝ y 0≤y)
    (λ e 0<e →
  let
    X : RealI
    X = expℝ x 0≤x

    0≤X : 0ℝ ≤ℝ X
    0≤X = expℝ-nonNeg x 0≤x

    Y : RealI
    Y = expℝ y 0≤y

    -- Rational points above the two arguments plus one.
    --
    -- 两个自变元加一之上的有理点。
    x1 : RealI
    x1 = x +ℝ embedℚ 1ℚ

    0≤x1 : 0ℝ ≤ℝ x1
    0≤x1 = 0≤add x (embedℚ 1ℚ) 0≤x (<⇒≤ℝ (0<embedℚ 1ℚ 0<1))

    y1 : RealI
    y1 = y +ℝ embedℚ 1ℚ

    0≤y1 : 0ℝ ≤ℝ y1
    0≤y1 = 0≤add y (embedℚ 1ℚ) 0≤y (<⇒≤ℝ (0<embedℚ 1ℚ 0<1))

    x1<x1p1 : x1 <ℝ x1 +ℝ embedℚ 1ℚ
    x1<x1p1 = lt-self-plus-one x1

    y1<y1p1 : y1 <ℝ y1 +ℝ embedℚ 1ℚ
    y1<y1p1 = lt-self-plus-one y1

    upx : Σ ℚ (λ t → (x1 <ℝ embedℚ t) × (embedℚ t <ℝ x1 +ℝ embedℚ 1ℚ))
    upx = dense {x1} {x1 +ℝ embedℚ 1ℚ} x1<x1p1

    upy : Σ ℚ (λ t → (y1 <ℝ embedℚ t) × (embedℚ t <ℝ y1 +ℝ embedℚ 1ℚ))
    upy = dense {y1} {y1 +ℝ embedℚ 1ℚ} y1<y1p1

    U₀ : ℚ
    U₀ = proj₁ upx

    x1<U₀ : x1 <ℝ embedℚ U₀
    x1<U₀ = proj₁ (proj₂ upx)

    V₀ : ℚ
    V₀ = proj₁ upy

    y1<V₀ : y1 <ℝ embedℚ V₀
    y1<V₀ = proj₁ (proj₂ upy)

    0≤U₀ : 0ℚ ≤ U₀
    0≤U₀ = <⇒≤ (embedℚ-reflect 0ℚ U₀ (≤ℝ-<trans 0≤x1 x1<U₀))

    0≤V₀ : 0ℚ ≤ V₀
    0≤V₀ = <⇒≤ (embedℚ-reflect 0ℚ V₀ (≤ℝ-<trans 0≤y1 y1<V₀))

    U : ℚ
    U = U₀ + V₀

    0≤U : 0ℚ ≤ U
    0≤U = ≤-trans 0≤U₀ (le-add-right U₀ V₀ 0≤V₀)

    ub : Σ ℚ (λ B → (j : ℕ) → expPartial U j ≤ B)
    ub = expPartial-bound U 0≤U 1ℚ 0<1

    B : ℚ
    B = proj₁ ub

    bndU : (j : ℕ) → expPartial U j ≤ B
    bndU = proj₂ ub

    0≤B : 0ℚ ≤ B
    0≤B = subst (λ z → z ≤ B) (expPartial-zero U) (bndU zero)

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤2 : 0ℚ ≤ 1ℚ + 1ℚ
    0≤2 = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ 1ℚ (<⇒≤ 0<1))

    cc : ℚ
    cc = ((1ℚ + 1ℚ) * (1ℚ + B)) + 1ℚ

    0≤cc : 0ℚ ≤ cc
    0≤cc = ≤-trans (prod-nonNeg (1ℚ + 1ℚ) (1ℚ + B) 0≤2 0≤1B)
             (le-add-right ((1ℚ + 1ℚ) * (1ℚ + B)) 1ℚ (<⇒≤ 0<1))

    sh : Σ ℕ (λ j → ε j * cc < e)
    sh = rat-shrink cc 0≤cc e 0<e

    jj : ℕ
    jj = proj₁ sh

    shr : ε jj * cc < e
    shr = proj₂ sh

    hh : ℚ
    hh = ε jj

    0<hh : 0ℚ < hh
    0<hh = 0<ε jj

    0≤hh : 0ℚ ≤ hh
    0≤hh = <⇒≤ 0<hh

    hh≤1 : hh ≤ 1ℚ
    hh≤1 = ε-≤-1 jj

    -- The same width serves both arguments.
    --
    -- 两个自变元共用同一个宽度。
    winx : Σ ℚ (λ p → (0ℚ ≤ p)
                   × (embedℚ p ≤ℝ x × x ≤ℝ embedℚ (p + hh)))
    winx = rat-window-nonNeg x 0≤x hh 0<hh

    winy : Σ ℚ (λ p → (0ℚ ≤ p)
                   × (embedℚ p ≤ℝ y × y ≤ℝ embedℚ (p + hh)))
    winy = rat-window-nonNeg y 0≤y hh 0<hh

    a : ℚ
    a = proj₁ winx

    0≤a : 0ℚ ≤ a
    0≤a = proj₁ (proj₂ winx)

    a≤x : embedℚ a ≤ℝ x
    a≤x = proj₁ (proj₂ (proj₂ winx))

    x≤ah : x ≤ℝ embedℚ (a + hh)
    x≤ah = proj₂ (proj₂ (proj₂ winx))

    b : ℚ
    b = proj₁ winy

    0≤b : 0ℚ ≤ b
    0≤b = proj₁ (proj₂ winy)

    b≤y : embedℚ b ≤ℝ y
    b≤y = proj₁ (proj₂ (proj₂ winy))

    y≤bh : y ≤ℝ embedℚ (b + hh)
    y≤bh = proj₂ (proj₂ (proj₂ winy))

    q : ℚ
    q = a + b

    0≤q : 0ℚ ≤ q
    0≤q = ≤-trans 0≤a (le-add-right a b 0≤b)

    w : ℚ
    w = hh + hh

    0≤w : 0ℚ ≤ w
    0≤w = ≤-trans 0≤hh (le-add-right hh hh 0≤hh)

    0≤qw : 0ℚ ≤ q + w
    0≤qw = ≤-trans 0≤q (le-add-right q w 0≤w)

    -- The endpoints of the pair window stay inside the bounded point.
    --
    -- 并窗的端点落在受界的点之内。
    a1≈ : embedℚ a +ℝ embedℚ 1ℚ ≈ℝ embedℚ (a + 1ℚ)
    a1≈ = sum-emb a 1ℚ

    a1≤x1 : embedℚ (a + 1ℚ) ≤ℝ x +ℝ embedℚ 1ℚ
    a1≤x1 = ≤ℝ-resp-≈ a1≈ (≈ℝ-refl {x +ℝ embedℚ 1ℚ})
              (≤ℝ-+-mono {embedℚ a} {x} {embedℚ 1ℚ} a≤x)

    a1h<U₀ : embedℚ (a + 1ℚ) <ℝ embedℚ U₀
    a1h<U₀ = ≤ℝ-<trans a1≤x1 x1<U₀

    a1<U₀ : a + 1ℚ < U₀
    a1<U₀ = embedℚ-reflect (a + 1ℚ) U₀ a1h<U₀

    b1≈ : embedℚ b +ℝ embedℚ 1ℚ ≈ℝ embedℚ (b + 1ℚ)
    b1≈ = sum-emb b 1ℚ

    b1≤y1 : embedℚ (b + 1ℚ) ≤ℝ y +ℝ embedℚ 1ℚ
    b1≤y1 = ≤ℝ-resp-≈ b1≈ (≈ℝ-refl {y +ℝ embedℚ 1ℚ})
              (≤ℝ-+-mono {embedℚ b} {y} {embedℚ 1ℚ} b≤y)

    b1h<V₀ : embedℚ (b + 1ℚ) <ℝ embedℚ V₀
    b1h<V₀ = ≤ℝ-<trans b1≤y1 y1<V₀

    b1<V₀ : b + 1ℚ < V₀
    b1<V₀ = embedℚ-reflect (b + 1ℚ) V₀ b1h<V₀

    qw≤U : q + w ≤ U
    qw≤U = qbelow a b hh U₀ V₀ hh≤1 (<⇒≤ a1<U₀) (<⇒≤ b1<V₀)

    bndq : (j : ℕ) → expPartial (q + w) j ≤ B
    bndq j = ≤-trans (expPartial-le-param (q + w) U 0≤qw qw≤U j) (bndU j)

    -- The point at the lower rational end of the pair window.
    --
    -- 并窗有理下端处的那个点。
    X0 : RealI
    X0 = x +ℝ embedℚ b

    0≤X0 : 0ℝ ≤ℝ X0
    0≤X0 = 0≤shift x 0≤x b 0≤b

    wpl : embedℚ q ≤ℝ X0
    wpl = ≤ℝ-resp-≈ (sum-emb a b) (≈ℝ-refl {x +ℝ embedℚ b})
            (≤ℝ-+-mono {embedℚ a} {x} {embedℚ b} a≤x)

    wqu : X0 ≤ℝ embedℚ (q + w)
    wqu = ≤ℝ-trans
            (≤ℝ-resp-≈ (≈ℝ-refl {x +ℝ embedℚ b})
              (sum-emb (a + hh) b)
              (≤ℝ-+-mono {x} {embedℚ (a + hh)} {embedℚ b} x≤ah))
            (embedℚ-≤ ((a + hh) + b) (q + w) (qshift a b hh 0≤hh))

    wypl : embedℚ q ≤ℝ x +ℝ y
    wypl = ≤ℝ-resp-≈ (sum-emb a b) (≈ℝ-refl {x +ℝ y})
             (≤ℝ-trans (≤ℝ-+-mono {embedℚ a} {x} {embedℚ b} a≤x)
               (≤ℝ-+-monoˡ {embedℚ b} {y} {x} b≤y))

    wyqu : x +ℝ y ≤ℝ embedℚ (q + w)
    wyqu = ≤ℝ-trans
             (≤ℝ-resp-≈ (≈ℝ-refl {x +ℝ y})
               (sum-emb (a + hh) (b + hh))
               (≤ℝ-trans (≤ℝ-+-mono {x} {embedℚ (a + hh)} {y} x≤ah)
                 (≤ℝ-+-monoˡ {y} {embedℚ (b + hh)} {embedℚ (a + hh)} y≤bh)))
             (embedℚ-≤ ((a + hh) + (b + hh)) (q + w)
               (≤-reflexive (qdouble a b hh)))

    -- The tolerance supplied by the closeness statement.
    --
    -- 邻近关系给出的容差。
    d : ℚ
    d = w * (1ℚ + B) + hh

    d≤e : d ≤ e
    d≤e = ≤-trans (≤-reflexive (qbudget hh B)) (<⇒≤ shr)

    cX0 : Close d (expℝ (x +ℝ y) (0≤add x y 0≤x 0≤y)) (expℝ X0 0≤X0)
    cX0 = expℝ-close-window q w 0≤q 0≤w B bndq hh 0<hh
            (x +ℝ y) X0 (0≤add x y 0≤x 0≤y) 0≤X0 wypl wyqu wpl wqu

    -- Closing the argument chain.
    --
    -- 收束论证链。
    Y1 : RealI
    Y1 = expℝ (embedℚ b) (embed-nonNeg b 0≤b)

    Y1≤Y : Y1 ≤ℝ Y
    Y1≤Y = expℝ-mono (embedℚ b) y (embed-nonNeg b 0≤b) 0≤y b≤y

    XY1 : RealI
    XY1 = X *ℝ Y1

    XY : RealI
    XY = X *ℝ Y

    P0 : expℝ X0 0≤X0 ≤ℝ XY1
    P0 = expℝ-add-shift-le x 0≤x b 0≤b

    M1 : Y1 *ℝ X ≤ℝ Y *ℝ X
    M1 = *ℝ-≤-mono Y1 Y X Y1≤Y 0≤X

    P1 : XY1 ≤ℝ XY
    P1 = ≤ℝ-resp-≈ (≈ℝ-sym (*ℝ-comm X Y1)) (≈ℝ-sym (*ℝ-comm X Y)) M1

    P2 : XY1 +ℝ embedℚ d ≤ℝ XY +ℝ embedℚ d
    P2 = ≤ℝ-+-mono {XY1} {XY} {embedℚ d} P1

    P3 : XY +ℝ embedℚ d ≤ℝ XY +ℝ embedℚ e
    P3 = ≤ℝ-+-monoˡ {embedℚ d} {embedℚ e} {XY} (embedℚ-≤ d e d≤e)

    PQ : expℝ (x +ℝ y) (0≤add x y 0≤x 0≤y) ≤ℝ XY +ℝ embedℚ e
    PQ = ≤ℝ-trans
           (close-below d (expℝ (x +ℝ y) (0≤add x y 0≤x 0≤y)) (expℝ X0 0≤X0) cX0)
           (≤ℝ-trans
             (≤ℝ-+-mono {expℝ X0 0≤X0} {XY1} {embedℚ d} P0)
             (≤ℝ-trans P2 P3))
  in
    PQ)

------------------------------------------------------------------------
-- The exponential under a rational translation
--
-- 有理平移下的指数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.AddShift where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_)
open import Data.Rational.Properties using
  (≤-total; ≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; <⇒≤; +-mono-≤
  ; +-identityˡ; +-identityʳ; +-assoc; +-comm; +-mono-<-≤; *-assoc; *-comm
  ; *-identityʳ; *-distribˡ-+; *-distribʳ-+)
open import Data.Sum using (_⊎_; [_,_])
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst)

open import Base.RationalRing using (0<1; 0≤1)
open import Real using (embed; half; ε; 0<ε; 0<embed)
open import Real.Archimedean using (rat-shrink; ε-≤-1)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-comm; +ℝ-assoc; sub-add-cancelℝ; +ℝ-identityˡ)
open import Real.Interval.Continuity using (Close; 0<embedℚ)
open import Real.Interval.DensityArch using (dense; ≤ℝ-of-slack)
open import Real.Interval.Embed using (embedℚ-+; embedℚ-*; embedℚ-cong)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Elementary.Exp using (expℝ)
open import Real.Interval.Elementary.ExpLaws using
  (expℝ-close-window; expℝ-nonNeg; expℝ-bound-nat)
open import Real.Interval.Elementary.ExpRat using (embed-nonNeg)
open import Real.Interval.Exp.Core using (expPartial; expPartial-zero)
open import Real.Interval.Exp.Lipschitz using
  (expPartial-bound; prod-nonNeg)
open import Real.Archimedean using (le-add-right)
open import Real.Interval.Exp.Order using (expPartial-le-param)
open import Real.Interval.Exp.AddRat using (expℝ-add-rat)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Order using (*ℝ-≤-mono; +ℝ-cong; ≈-<-respʳ)
open import Real.Interval.Mul.Laws using (*ℝ-comm; *ℝ-distribʳ-+)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (<⇒≤ℝ; ≈⇒≤ℝ; ≤ℝ-refl; ≤ℝ-resp-≈; ≤ℝ-+-mono; ≤ℝ-+-monoˡ; ≤ℝ-antisym
  ; ≤ℝ-<trans; <-≤ℝ-trans)
open import Real.Interval.OrderLaws using (≈-<-resp; <-+mono)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤; embedℚ-reflect)

------------------------------------------------------------------------
-- A rational window of prescribed width above a nonnegative real
--
-- 非负实数上方给定宽度的有理窗

-- Density alone may return a negative left endpoint, which the exponential
-- cannot take as an argument. The endpoint is therefore replaced by zero in
-- the branch where it is nonpositive: there the real itself lies below the
-- width, so the window starting at zero still contains it. The width taken
-- for the density point is the same as the width of the window, so no
-- rescaling of the endpoints is needed afterwards. The sign test lives in a
-- separate definition so that its decision procedure sees the endpoint as a
-- variable; comparing a projected endpoint directly would unfold the density
-- search.
--
-- 单靠稠密性可能取到负的左端点，而指数不接受负的有理参数。故在端点非正的分支
-- 改用零：此时实数本身落在窗宽之内，从零开始的窗仍然含它。取稠密点用的窗宽与
-- 窗本身的宽度相同，故两端点事后无须再作换算。符号判定独立成一条定义，好让判定
-- 过程看到的端点是变量；直接比较投影出来的端点会展开稠密性的搜索。
rat-window-at : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (hh : ℚ) (0<hh : 0ℚ < hh)
                (p : ℚ) (xhh<p : x -ℝ embedℚ hh <ℝ embedℚ p)
                (p<x : embedℚ p <ℝ x)
              → Σ ℚ (λ p' → (0ℚ ≤ p')
                   × (embedℚ p' ≤ℝ x × x ≤ℝ embedℚ (p' + hh)))
rat-window-at x 0≤x hh 0<hh p xhh<p p<x =
  let
    shift : (x -ℝ embedℚ hh) +ℝ embedℚ hh <ℝ embedℚ p +ℝ embedℚ hh
    shift = <-+mono (x -ℝ embedℚ hh) (embedℚ p) (embedℚ hh) xhh<p

    x<ph₀ : x <ℝ embedℚ p +ℝ embedℚ hh
    x<ph₀ = ≈-<-resp (sub-add-cancelℝ x (embedℚ hh)) shift

    x<ph : x <ℝ embedℚ (p + hh)
    x<ph = ≈-<-respʳ (≈ℝ-sym (embedℚ-+ p hh)) x<ph₀

    atP : 0ℚ ≤ p
        → Σ ℚ (λ p' → (0ℚ ≤ p')
             × (embedℚ p' ≤ℝ x × x ≤ℝ embedℚ (p' + hh)))
    atP p≥0 = p , (p≥0 , (<⇒≤ℝ p<x , <⇒≤ℝ x<ph))

    atZero : p ≤ 0ℚ
           → Σ ℚ (λ p' → (0ℚ ≤ p')
                × (embedℚ p' ≤ℝ x × x ≤ℝ embedℚ (p' + hh)))
    atZero p≤0 =
      let
        xh<0 : x -ℝ embedℚ hh <ℝ 0ℝ
        xh<0 = <-≤ℝ-trans xhh<p (embedℚ-≤ p 0ℚ p≤0)

        x<hh₀ : (x -ℝ embedℚ hh) +ℝ embedℚ hh <ℝ 0ℝ +ℝ embedℚ hh
        x<hh₀ = <-+mono (x -ℝ embedℚ hh) 0ℝ (embedℚ hh) xh<0

        x<hh : x <ℝ embedℚ hh
        x<hh = ≈-<-resp (sub-add-cancelℝ x (embedℚ hh))
                 (≈-<-respʳ (+ℝ-identityˡ (embedℚ hh)) x<hh₀)

        rename : embedℚ hh ≈ℝ embedℚ (0ℚ + hh)
        rename = embedℚ-cong (sym (+-identityˡ hh))

        x≤0hh : x ≤ℝ embedℚ (0ℚ + hh)
        x≤0hh = ≤ℝ-resp-≈ (≈ℝ-refl {x}) rename (<⇒≤ℝ x<hh)
      in
        0ℚ , (≤-refl {0ℚ} , (0≤x , x≤0hh))
  in
    [ atZero , atP ] (≤-total p 0ℚ)

------------------------------------------------------------------------
-- The window assembled from a density point
--
-- 由稠密点装配的窗

-- The density point is taken below the real, within the width, and the
-- window proper is produced by the sign split above.
--
-- 稠密点取在实数下方、距其不超过窗宽；窗本身由上面的符号分支产生。
rat-window-nonNeg : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (hh : ℚ) (0<hh : 0ℚ < hh)
                  → Σ ℚ (λ p → (0ℚ ≤ p)
                       × (embedℚ p ≤ℝ x × x ≤ℝ embedℚ (p + hh)))
rat-window-nonNeg x 0≤x hh 0<hh =
  let
    bot : x -ℝ embedℚ hh <ℝ x
    bot = ≈-<-respʳ (sub-add-cancelℝ x (embedℚ hh))
            (≈-<-resp (+ℝ-identityˡ (x -ℝ embedℚ hh))
              (≈-<-respʳ (+ℝ-comm (embedℚ hh) (x -ℝ embedℚ hh))
                (<-+mono 0ℝ (embedℚ hh) (x -ℝ embedℚ hh)
                  (0<embedℚ hh 0<hh))))

    down : Σ ℚ (λ p → (x -ℝ embedℚ hh <ℝ embedℚ p) × (embedℚ p <ℝ x))
    down = dense {x -ℝ embedℚ hh} {x} bot
  in
    rat-window-at x 0≤x hh 0<hh (proj₁ down)
      (proj₁ (proj₂ down)) (proj₂ (proj₂ down))

------------------------------------------------------------------------
-- Nonnegativity under a rational translation
--
-- 有理平移下的非负性

-- Adding a nonnegative rational to a nonnegative real keeps it
-- nonnegative: the zero of the rationals sits below the added term and
-- the empty real sum sits below that term.
--
-- 非负实数加上非负有理点仍非负：有理零低于所加项，空的实数和又低于该项。
0≤shift : (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
        → 0ℝ ≤ℝ x +ℝ embedℚ q
0≤shift x 0≤x q 0≤q =
  ≤ℝ-trans (≤ℝ-trans (embedℚ-≤ 0ℚ q 0≤q)
             (≈⇒≤ℝ (≈ℝ-sym (+ℝ-identityˡ (embedℚ q)))))
    (≤ℝ-+-mono {0ℝ} {x} {embedℚ q} 0≤x)

------------------------------------------------------------------------
-- The assembly of the two estimates at a window endpoint
--
-- 窗端点处两个估计的装配

-- Everything after the window is proved with the endpoint and the width
-- as variables: forming rational sums out of a projected endpoint would
-- unfold the density search, while rational arithmetic on variables is
-- decided once and for all. The bound point, its bound and the budget
-- are supplied by the caller.
--
-- 窗之后的部分以端点和窗宽为变量来证：以投影出来的端点构造有理和会展开
-- 稠密性的搜索，而在变量上的有理算术只需判定一次。界点、其界与预算由调用方
-- 提供。
expℝ-add-shift-tail :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
    (e : ℚ) (0<e : 0ℚ < e)
    (hh : ℚ) (0<hh : 0ℚ < hh) (0≤hh : 0ℚ ≤ hh) (hh≤1 : hh ≤ 1ℚ)
    (p : ℚ) (0≤p : 0ℚ ≤ p) (p≤x : embedℚ p ≤ℝ x)
    (x≤ph : x ≤ℝ embedℚ (p + hh))
    (U₀ : ℚ) (B : ℚ) (0≤B : 0ℚ ≤ B)
    (bndU : (j : ℕ) → expPartial (U₀ + q) j ≤ B)
    (Nq : ℚ) (0≤Nq : 0ℚ ≤ Nq)
    (Q≤Nq : expℝ (embedℚ q) (embed-nonNeg q 0≤q) ≤ℝ embedℚ Nq)
    (p1<U₀ : p + 1ℚ < U₀)
    (bud' : (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e)
  → (expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q)
      ≤ℝ (expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)) +ℝ embedℚ e)
    × ((expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q))
      ≤ℝ expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q) +ℝ embedℚ e)
expℝ-add-shift-tail x 0≤x q 0≤q e 0<e hh 0<hh 0≤hh hh≤1 p 0≤p p≤x x≤ph
    U₀ B 0≤B bndU Nq 0≤Nq Q≤Nq p1<U₀ bud' =
  let
    eq : RealI
    eq = embedℚ q

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    xq : RealI
    xq = x +ℝ eq

    0≤xq : 0ℝ ≤ℝ xq
    0≤xq = 0≤shift x 0≤x q 0≤q

    X : RealI
    X = expℝ x 0≤x

    Q : RealI
    Q = expℝ eq 0≤eq

    0≤Q : 0ℝ ≤ℝ Q
    0≤Q = expℝ-nonNeg eq 0≤eq

    Cx : RealI
    Cx = expℝ xq 0≤xq

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤ph : 0ℚ ≤ p + hh
    0≤ph = ≤-trans 0≤p (le-add-right p hh 0≤hh)

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)

    0≤pqh : 0ℚ ≤ (p + q) + hh
    0≤pqh = ≤-trans 0≤pq (le-add-right (p + q) hh 0≤hh)

    ph≤p1 : p + hh ≤ p + 1ℚ
    ph≤p1 = +-mono-≤ (≤-refl {p}) hh≤1

    ph≤U₀ : p + hh ≤ U₀
    ph≤U₀ = ≤-trans ph≤p1 (<⇒≤ p1<U₀)

    ph≤U : p + hh ≤ U₀ + q
    ph≤U = ≤-trans ph≤U₀ (le-add-right U₀ q 0≤q)

    re₀ : (p + q) + hh ≡ p + (q + hh)
    re₀ = +-assoc p q hh

    re₁ : p + (q + hh) ≡ p + (hh + q)
    re₁ = cong (λ z → p + z) (+-comm q hh)

    re₂ : p + (hh + q) ≡ (p + hh) + q
    re₂ = sym (+-assoc p hh q)

    re : (p + q) + hh ≡ (p + hh) + q
    re = trans re₀ (trans re₁ re₂)

    pqh≤phq : (p + q) + hh ≤ (p + hh) + q
    pqh≤phq = ≤-reflexive re

    phq≤Uq : (p + hh) + q ≤ U₀ + q
    phq≤Uq = +-mono-≤ ph≤U₀ (≤-refl {q})

    pqh≤U : (p + q) + hh ≤ U₀ + q
    pqh≤U = ≤-trans pqh≤phq phq≤Uq

    bnd₀ : (j : ℕ) → expPartial (p + hh) j ≤ B
    bnd₀ j = ≤-trans (expPartial-le-param (p + hh) (U₀ + q) 0≤ph ph≤U j) (bndU j)

    bnd₁ : (j : ℕ) → expPartial ((p + q) + hh) j ≤ B
    bnd₁ j = ≤-trans (expPartial-le-param ((p + q) + hh) (U₀ + q) 0≤pqh pqh≤U j)
               (bndU j)

    ep₀ : RealI
    ep₀ = embedℚ p

    0≤ep₀ : 0ℝ ≤ℝ ep₀
    0≤ep₀ = embed-nonNeg p 0≤p

    ep : RealI
    ep = expℝ ep₀ 0≤ep₀

    ep≤ph : embedℚ p ≤ℝ embedℚ (p + hh)
    ep≤ph = embedℚ-≤ p (p + hh) (le-add-right p hh 0≤hh)

    cX : Close (hh * (1ℚ + B) + hh) X ep
    cX = expℝ-close-window p hh 0≤p 0≤hh B bnd₀ hh 0<hh x ep₀ 0≤x 0≤ep₀
           p≤x x≤ph (≤ℝ-refl {ep₀}) ep≤ph

    pq≤xq₀ : embedℚ p +ℝ embedℚ q ≤ℝ x +ℝ embedℚ q
    pq≤xq₀ = ≤ℝ-+-mono {embedℚ p} {x} {embedℚ q} p≤x

    pq≈ : embedℚ (p + q) ≈ℝ embedℚ p +ℝ embedℚ q
    pq≈ = embedℚ-+ p q

    epq : RealI
    epq = embedℚ (p + q)

    0≤epq : 0ℝ ≤ℝ epq
    0≤epq = embed-nonNeg (p + q) 0≤pq

    pq≤xq : epq ≤ℝ xq
    pq≤xq = ≤ℝ-resp-≈ (≈ℝ-sym pq≈) (≈ℝ-refl {xq}) pq≤xq₀

    xq≤phq₀ : x +ℝ embedℚ q ≤ℝ embedℚ (p + hh) +ℝ embedℚ q
    xq≤phq₀ = ≤ℝ-+-mono {x} {embedℚ (p + hh)} {embedℚ q} x≤ph

    phq≈ : embedℚ (p + hh) +ℝ embedℚ q ≈ℝ embedℚ ((p + hh) + q)
    phq≈ = ≈ℝ-sym (embedℚ-+ (p + hh) q)

    xq≤phq : xq ≤ℝ embedℚ ((p + hh) + q)
    xq≤phq = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) phq≈ xq≤phq₀

    xq≤pqh : xq ≤ℝ embedℚ ((p + q) + hh)
    xq≤pqh = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) (embedℚ-cong (sym re)) xq≤phq

    epq≤pqh : embedℚ (p + q) ≤ℝ embedℚ ((p + q) + hh)
    epq≤pqh = embedℚ-≤ (p + q) ((p + q) + hh)
                (le-add-right (p + q) hh 0≤hh)

    PQ : RealI
    PQ = expℝ epq 0≤epq

    cC : Close (hh * (1ℚ + B) + hh) Cx PQ
    cC = expℝ-close-window (p + q) hh 0≤pq 0≤hh B bnd₁ hh 0<hh xq epq 0≤xq 0≤epq
           pq≤xq xq≤pqh (≤ℝ-refl {epq}) epq≤pqh

    dv : ℚ
    dv = hh * (1ℚ + B) + hh

    0≤dv : 0ℚ ≤ dv
    0≤dv = ≤-trans (prod-nonNeg hh (1ℚ + B) 0≤hh 0≤1B)
             (le-add-right (hh * (1ℚ + B)) hh 0≤hh)

    0≤edv : 0ℝ ≤ℝ embedℚ dv
    0≤edv = embed-nonNeg dv 0≤dv

    -- The two components of the first window.
    --
    -- 第一个窗口的两个分量。
    X<Pdv : X <ℝ ep +ℝ embedℚ dv
    X<Pdv = ≈-<-resp (sub-add-cancelℝ X (embedℚ dv))
              (<-+mono (X -ℝ embedℚ dv) ep (embedℚ dv) (proj₁ cX))

    X≤Pdv : X ≤ℝ ep +ℝ embedℚ dv
    X≤Pdv = <⇒≤ℝ X<Pdv

    P≤Xdv : ep ≤ℝ X +ℝ embedℚ dv
    P≤Xdv = <⇒≤ℝ (proj₂ cX)

    C<PQdv : Cx <ℝ PQ +ℝ embedℚ dv
    C<PQdv = ≈-<-resp (sub-add-cancelℝ Cx (embedℚ dv))
               (<-+mono (Cx -ℝ embedℚ dv) PQ (embedℚ dv) (proj₁ cC))

    C≤PQdv : Cx ≤ℝ PQ +ℝ embedℚ dv
    C≤PQdv = <⇒≤ℝ C<PQdv

    PQ≤Cdv : PQ ≤ℝ Cx +ℝ embedℚ dv
    PQ≤Cdv = <⇒≤ℝ (proj₂ cC)

    -- The rational additivity law at the two window endpoints.
    --
    -- 两个窗口端点处的有理加法律。
    rat : PQ ≈ℝ ep *ℝ Q
    rat = expℝ-add-rat p q 0≤p 0≤q


    -- The two rational products with the exponential at `q`.
    --
    -- 与 `q` 处指数相乘的两个有理积。
    dQ≤dNq : embedℚ dv *ℝ Q ≤ℝ embedℚ dv *ℝ embedℚ Nq
    dQ≤dNq = ≤ℝ-resp-≈ (*ℝ-comm Q (embedℚ dv))
              (*ℝ-comm (embedℚ Nq) (embedℚ dv))
              (*ℝ-≤-mono Q (embedℚ Nq) (embedℚ dv) Q≤Nq 0≤edv)

    -- The lower estimate `C ≤ X * Q + e`.
    --
    -- 下界估计 `C ≤ X * Q + e`。
    ch1 : Cx ≤ℝ PQ +ℝ embedℚ dv
    ch1 = C≤PQdv

    ch2 : PQ +ℝ embedℚ dv ≤ℝ (ep *ℝ Q) +ℝ embedℚ dv
    ch2 = ≤ℝ-+-mono {PQ} {ep *ℝ Q} {embedℚ dv} (≈⇒≤ℝ rat)

    mR : ep *ℝ Q ≤ℝ (X +ℝ embedℚ dv) *ℝ Q
    mR = *ℝ-≤-mono ep (X +ℝ embedℚ dv) Q P≤Xdv 0≤Q

    ch3 : (ep *ℝ Q) +ℝ embedℚ dv ≤ℝ ((X +ℝ embedℚ dv) *ℝ Q) +ℝ embedℚ dv
    ch3 = ≤ℝ-+-mono {ep *ℝ Q} {(X +ℝ embedℚ dv) *ℝ Q} {embedℚ dv} mR

    dist : (X +ℝ embedℚ dv) *ℝ Q ≈ℝ X *ℝ Q +ℝ embedℚ dv *ℝ Q
    dist = *ℝ-distribʳ-+ Q X (embedℚ dv)

    ch4 : ((X +ℝ embedℚ dv) *ℝ Q) +ℝ embedℚ dv
        ≤ℝ (X *ℝ Q +ℝ embedℚ dv *ℝ Q) +ℝ embedℚ dv
    ch4 = ≤ℝ-+-mono {(X +ℝ embedℚ dv) *ℝ Q} {X *ℝ Q +ℝ embedℚ dv *ℝ Q}
            {embedℚ dv} (≈⇒≤ℝ dist)

    ch5 : (X *ℝ Q +ℝ embedℚ dv *ℝ Q) +ℝ embedℚ dv
        ≤ℝ (X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq) +ℝ embedℚ dv
    ch5 = ≤ℝ-+-mono {X *ℝ Q +ℝ embedℚ dv *ℝ Q}
            {X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq} {embedℚ dv}
            (≤ℝ-+-monoˡ {embedℚ dv *ℝ Q} {embedℚ dv *ℝ embedℚ Nq} {X *ℝ Q} dQ≤dNq)

    ch6 : (X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq) +ℝ embedℚ dv
        ≈ℝ (X *ℝ Q +ℝ embedℚ (dv * Nq)) +ℝ embedℚ dv
    ch6 = +ℝ-cong (+ℝ-cong (≈ℝ-refl {X *ℝ Q}) (≈ℝ-sym (embedℚ-* dv Nq)))
            (≈ℝ-refl {embedℚ dv})

    ch7 : (X *ℝ Q +ℝ embedℚ (dv * Nq)) +ℝ embedℚ dv
        ≈ℝ X *ℝ Q +ℝ embedℚ ((dv * Nq) + dv)
    ch7 = ≈ℝ-trans (+ℝ-assoc (X *ℝ Q) (embedℚ (dv * Nq)) (embedℚ dv))
            (+ℝ-cong (≈ℝ-refl {X *ℝ Q}) (≈ℝ-sym (embedℚ-+ (dv * Nq) dv)))

    ch8 : X *ℝ Q +ℝ embedℚ ((dv * Nq) + dv) ≤ℝ X *ℝ Q +ℝ embedℚ e
    ch8 = ≤ℝ-+-monoˡ {embedℚ ((dv * Nq) + dv)} {embedℚ e} {X *ℝ Q}
            (embedℚ-≤ ((dv * Nq) + dv) e bud')

    le-part : Cx ≤ℝ X *ℝ Q +ℝ embedℚ e
    le-part = ≤ℝ-trans ch1
                (≤ℝ-trans ch2
                  (≤ℝ-trans ch3
                    (≤ℝ-trans ch4
                      (≤ℝ-trans ch5
                        (≤ℝ-trans (≈⇒≤ℝ ch6)
                          (≤ℝ-trans (≈⇒≤ℝ ch7) ch8))))))

    -- The upper estimate `X * Q ≤ C + e`.
    --
    -- 上界估计 `X * Q ≤ C + e`。
    g1 : X *ℝ Q ≤ℝ (ep +ℝ embedℚ dv) *ℝ Q
    g1 = *ℝ-≤-mono X (ep +ℝ embedℚ dv) Q X≤Pdv 0≤Q

    g2 : (ep +ℝ embedℚ dv) *ℝ Q ≈ℝ ep *ℝ Q +ℝ embedℚ dv *ℝ Q
    g2 = *ℝ-distribʳ-+ Q ep (embedℚ dv)

    g3 : ep *ℝ Q +ℝ embedℚ dv *ℝ Q ≤ℝ PQ +ℝ embedℚ dv *ℝ Q
    g3 = ≤ℝ-+-mono {ep *ℝ Q} {PQ} {embedℚ dv *ℝ Q}
           (≈⇒≤ℝ (≈ℝ-sym rat))

    g4 : PQ +ℝ embedℚ dv *ℝ Q ≤ℝ (Cx +ℝ embedℚ dv) +ℝ embedℚ dv *ℝ Q
    g4 = ≤ℝ-+-mono {PQ} {Cx +ℝ embedℚ dv} {embedℚ dv *ℝ Q} PQ≤Cdv

    g5 : (Cx +ℝ embedℚ dv) +ℝ embedℚ dv *ℝ Q
        ≈ℝ Cx +ℝ (embedℚ dv +ℝ embedℚ dv *ℝ Q)
    g5 = +ℝ-assoc Cx (embedℚ dv) (embedℚ dv *ℝ Q)

    g6 : Cx +ℝ (embedℚ dv +ℝ embedℚ dv *ℝ Q)
        ≈ℝ Cx +ℝ (embedℚ dv *ℝ Q +ℝ embedℚ dv)
    g6 = +ℝ-cong (≈ℝ-refl {Cx}) (+ℝ-comm (embedℚ dv) (embedℚ dv *ℝ Q))

    g7 : Cx +ℝ (embedℚ dv *ℝ Q +ℝ embedℚ dv)
        ≤ℝ Cx +ℝ (embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv)
    g7 = ≤ℝ-+-monoˡ {embedℚ dv *ℝ Q +ℝ embedℚ dv}
            {embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv} {Cx}
            (≤ℝ-+-mono {embedℚ dv *ℝ Q} {embedℚ dv *ℝ embedℚ Nq} {embedℚ dv} dQ≤dNq)

    g8 : Cx +ℝ (embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv)
        ≈ℝ Cx +ℝ (embedℚ (dv * Nq) +ℝ embedℚ dv)
    g8 = +ℝ-cong (≈ℝ-refl {Cx})
           (+ℝ-cong (≈ℝ-sym (embedℚ-* dv Nq)) (≈ℝ-refl {embedℚ dv}))

    g9 : Cx +ℝ (embedℚ (dv * Nq) +ℝ embedℚ dv)
        ≈ℝ Cx +ℝ embedℚ ((dv * Nq) + dv)
    g9 = +ℝ-cong (≈ℝ-refl {Cx}) (≈ℝ-sym (embedℚ-+ (dv * Nq) dv))

    g10 : Cx +ℝ embedℚ ((dv * Nq) + dv) ≤ℝ Cx +ℝ embedℚ e
    g10 = ≤ℝ-+-monoˡ {embedℚ ((dv * Nq) + dv)} {embedℚ e} {Cx}
            (embedℚ-≤ ((dv * Nq) + dv) e bud')

    ge-part : X *ℝ Q ≤ℝ Cx +ℝ embedℚ e
    ge-part = ≤ℝ-trans g1
                (≤ℝ-trans (≈⇒≤ℝ g2)
                  (≤ℝ-trans g3
                    (≤ℝ-trans g4
                      (≤ℝ-trans (≈⇒≤ℝ g5)
                        (≤ℝ-trans (≈⇒≤ℝ g6)
                          (≤ℝ-trans g7
                            (≤ℝ-trans (≈⇒≤ℝ g8)
                              (≤ℝ-trans (≈⇒≤ℝ g9) g10))))))))
  in
    le-part , ge-part


------------------------------------------------------------------------
-- The lower half at one window endpoint
--
-- 一个窗端点处的下界

-- The window endpoint and the width enter as variables, so the
-- rational reading of the endpoint is never unfolded here.
--
-- 窗端点与窗宽以变量进入，端点的有理读数在此永不展开。
expℝ-add-shift-tail-le :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
    (e : ℚ) (0<e : 0ℚ < e)
    (hh : ℚ) (0<hh : 0ℚ < hh) (0≤hh : 0ℚ ≤ hh) (hh≤1 : hh ≤ 1ℚ)
    (p : ℚ) (0≤p : 0ℚ ≤ p) (p≤x : embedℚ p ≤ℝ x)
    (x≤ph : x ≤ℝ embedℚ (p + hh))
    (U₀ : ℚ) (B : ℚ) (0≤B : 0ℚ ≤ B)
    (bndU : (j : ℕ) → expPartial (U₀ + q) j ≤ B)
    (Nq : ℚ) (0≤Nq : 0ℚ ≤ Nq)
    (Q≤Nq : expℝ (embedℚ q) (embed-nonNeg q 0≤q) ≤ℝ embedℚ Nq)
    (p1<U₀ : p + 1ℚ < U₀)
    (bud' : (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e)  → expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q)
    ≤ℝ (expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)) +ℝ embedℚ e
expℝ-add-shift-tail-le x 0≤x q 0≤q e 0<e hh 0<hh 0≤hh hh≤1 p 0≤p p≤x x≤ph
    U₀ B 0≤B bndU Nq 0≤Nq Q≤Nq p1<U₀ bud' =
  let
    eq : RealI
    eq = embedℚ q

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    xq : RealI
    xq = x +ℝ eq

    0≤xq : 0ℝ ≤ℝ xq
    0≤xq = 0≤shift x 0≤x q 0≤q

    X : RealI
    X = expℝ x 0≤x

    Q : RealI
    Q = expℝ eq 0≤eq

    0≤Q : 0ℝ ≤ℝ Q
    0≤Q = expℝ-nonNeg eq 0≤eq

    Cx : RealI
    Cx = expℝ xq 0≤xq

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤ph : 0ℚ ≤ p + hh
    0≤ph = ≤-trans 0≤p (le-add-right p hh 0≤hh)

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)

    0≤pqh : 0ℚ ≤ (p + q) + hh
    0≤pqh = ≤-trans 0≤pq (le-add-right (p + q) hh 0≤hh)

    ph≤p1 : p + hh ≤ p + 1ℚ
    ph≤p1 = +-mono-≤ (≤-refl {p}) hh≤1

    ph≤U₀ : p + hh ≤ U₀
    ph≤U₀ = ≤-trans ph≤p1 (<⇒≤ p1<U₀)

    ph≤U : p + hh ≤ U₀ + q
    ph≤U = ≤-trans ph≤U₀ (le-add-right U₀ q 0≤q)

    re₀ : (p + q) + hh ≡ p + (q + hh)
    re₀ = +-assoc p q hh

    re₁ : p + (q + hh) ≡ p + (hh + q)
    re₁ = cong (λ z → p + z) (+-comm q hh)

    re₂ : p + (hh + q) ≡ (p + hh) + q
    re₂ = sym (+-assoc p hh q)

    re : (p + q) + hh ≡ (p + hh) + q
    re = trans re₀ (trans re₁ re₂)

    pqh≤phq : (p + q) + hh ≤ (p + hh) + q
    pqh≤phq = ≤-reflexive re

    phq≤Uq : (p + hh) + q ≤ U₀ + q
    phq≤Uq = +-mono-≤ ph≤U₀ (≤-refl {q})

    pqh≤U : (p + q) + hh ≤ U₀ + q
    pqh≤U = ≤-trans pqh≤phq phq≤Uq

    bnd₀ : (j : ℕ) → expPartial (p + hh) j ≤ B
    bnd₀ j = ≤-trans (expPartial-le-param (p + hh) (U₀ + q) 0≤ph ph≤U j) (bndU j)

    bnd₁ : (j : ℕ) → expPartial ((p + q) + hh) j ≤ B
    bnd₁ j = ≤-trans (expPartial-le-param ((p + q) + hh) (U₀ + q) 0≤pqh pqh≤U j)
               (bndU j)

    ep₀ : RealI
    ep₀ = embedℚ p

    0≤ep₀ : 0ℝ ≤ℝ ep₀
    0≤ep₀ = embed-nonNeg p 0≤p

    ep : RealI
    ep = expℝ ep₀ 0≤ep₀

    ep≤ph : embedℚ p ≤ℝ embedℚ (p + hh)
    ep≤ph = embedℚ-≤ p (p + hh) (le-add-right p hh 0≤hh)

    cX : Close (hh * (1ℚ + B) + hh) X ep
    cX = expℝ-close-window p hh 0≤p 0≤hh B bnd₀ hh 0<hh x ep₀ 0≤x 0≤ep₀
           p≤x x≤ph (≤ℝ-refl {ep₀}) ep≤ph

    pq≤xq₀ : embedℚ p +ℝ embedℚ q ≤ℝ x +ℝ embedℚ q
    pq≤xq₀ = ≤ℝ-+-mono {embedℚ p} {x} {embedℚ q} p≤x

    pq≈ : embedℚ (p + q) ≈ℝ embedℚ p +ℝ embedℚ q
    pq≈ = embedℚ-+ p q

    epq : RealI
    epq = embedℚ (p + q)

    0≤epq : 0ℝ ≤ℝ epq
    0≤epq = embed-nonNeg (p + q) 0≤pq

    pq≤xq : epq ≤ℝ xq
    pq≤xq = ≤ℝ-resp-≈ (≈ℝ-sym pq≈) (≈ℝ-refl {xq}) pq≤xq₀

    xq≤phq₀ : x +ℝ embedℚ q ≤ℝ embedℚ (p + hh) +ℝ embedℚ q
    xq≤phq₀ = ≤ℝ-+-mono {x} {embedℚ (p + hh)} {embedℚ q} x≤ph

    phq≈ : embedℚ (p + hh) +ℝ embedℚ q ≈ℝ embedℚ ((p + hh) + q)
    phq≈ = ≈ℝ-sym (embedℚ-+ (p + hh) q)

    xq≤phq : xq ≤ℝ embedℚ ((p + hh) + q)
    xq≤phq = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) phq≈ xq≤phq₀

    xq≤pqh : xq ≤ℝ embedℚ ((p + q) + hh)
    xq≤pqh = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) (embedℚ-cong (sym re)) xq≤phq

    epq≤pqh : embedℚ (p + q) ≤ℝ embedℚ ((p + q) + hh)
    epq≤pqh = embedℚ-≤ (p + q) ((p + q) + hh)
                (le-add-right (p + q) hh 0≤hh)

    PQ : RealI
    PQ = expℝ epq 0≤epq

    cC : Close (hh * (1ℚ + B) + hh) Cx PQ
    cC = expℝ-close-window (p + q) hh 0≤pq 0≤hh B bnd₁ hh 0<hh xq epq 0≤xq 0≤epq
           pq≤xq xq≤pqh (≤ℝ-refl {epq}) epq≤pqh

    dv : ℚ
    dv = hh * (1ℚ + B) + hh

    0≤dv : 0ℚ ≤ dv
    0≤dv = ≤-trans (prod-nonNeg hh (1ℚ + B) 0≤hh 0≤1B)
             (le-add-right (hh * (1ℚ + B)) hh 0≤hh)

    0≤edv : 0ℝ ≤ℝ embedℚ dv
    0≤edv = embed-nonNeg dv 0≤dv

    P≤Xdv : ep ≤ℝ X +ℝ embedℚ dv
    P≤Xdv = <⇒≤ℝ (proj₂ cX)

    C<PQdv : Cx <ℝ PQ +ℝ embedℚ dv
    C<PQdv = ≈-<-resp (sub-add-cancelℝ Cx (embedℚ dv))
               (<-+mono (Cx -ℝ embedℚ dv) PQ (embedℚ dv) (proj₁ cC))

    C≤PQdv : Cx ≤ℝ PQ +ℝ embedℚ dv
    C≤PQdv = <⇒≤ℝ C<PQdv

    -- The rational additivity law at the two window endpoints.
    --
    -- 两个窗口端点处的有理加法律。
    rat : PQ ≈ℝ ep *ℝ Q
    rat = expℝ-add-rat p q 0≤p 0≤q

    -- The two rational products with the exponential at `q`.
    --
    -- 与 `q` 处指数相乘的两个有理积。
    dQ≤dNq : embedℚ dv *ℝ Q ≤ℝ embedℚ dv *ℝ embedℚ Nq
    dQ≤dNq = ≤ℝ-resp-≈ (*ℝ-comm Q (embedℚ dv))
              (*ℝ-comm (embedℚ Nq) (embedℚ dv))
              (*ℝ-≤-mono Q (embedℚ Nq) (embedℚ dv) Q≤Nq 0≤edv)

    -- The lower estimate `C ≤ X * Q + e`.
    --
    -- 下界估计 `C ≤ X * Q + e`。
    ch1 : Cx ≤ℝ PQ +ℝ embedℚ dv
    ch1 = C≤PQdv

    ch2 : PQ +ℝ embedℚ dv ≤ℝ (ep *ℝ Q) +ℝ embedℚ dv
    ch2 = ≤ℝ-+-mono {PQ} {ep *ℝ Q} {embedℚ dv} (≈⇒≤ℝ rat)

    mR : ep *ℝ Q ≤ℝ (X +ℝ embedℚ dv) *ℝ Q
    mR = *ℝ-≤-mono ep (X +ℝ embedℚ dv) Q P≤Xdv 0≤Q

    ch3 : (ep *ℝ Q) +ℝ embedℚ dv ≤ℝ ((X +ℝ embedℚ dv) *ℝ Q) +ℝ embedℚ dv
    ch3 = ≤ℝ-+-mono {ep *ℝ Q} {(X +ℝ embedℚ dv) *ℝ Q} {embedℚ dv} mR

    dist : (X +ℝ embedℚ dv) *ℝ Q ≈ℝ X *ℝ Q +ℝ embedℚ dv *ℝ Q
    dist = *ℝ-distribʳ-+ Q X (embedℚ dv)

    ch4 : ((X +ℝ embedℚ dv) *ℝ Q) +ℝ embedℚ dv
        ≤ℝ (X *ℝ Q +ℝ embedℚ dv *ℝ Q) +ℝ embedℚ dv
    ch4 = ≤ℝ-+-mono {(X +ℝ embedℚ dv) *ℝ Q} {X *ℝ Q +ℝ embedℚ dv *ℝ Q}
            {embedℚ dv} (≈⇒≤ℝ dist)

    ch5 : (X *ℝ Q +ℝ embedℚ dv *ℝ Q) +ℝ embedℚ dv
        ≤ℝ (X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq) +ℝ embedℚ dv
    ch5 = ≤ℝ-+-mono {X *ℝ Q +ℝ embedℚ dv *ℝ Q}
            {X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq} {embedℚ dv}
            (≤ℝ-+-monoˡ {embedℚ dv *ℝ Q} {embedℚ dv *ℝ embedℚ Nq} {X *ℝ Q} dQ≤dNq)

    ch6 : (X *ℝ Q +ℝ embedℚ dv *ℝ embedℚ Nq) +ℝ embedℚ dv
        ≈ℝ (X *ℝ Q +ℝ embedℚ (dv * Nq)) +ℝ embedℚ dv
    ch6 = +ℝ-cong (+ℝ-cong (≈ℝ-refl {X *ℝ Q}) (≈ℝ-sym (embedℚ-* dv Nq)))
            (≈ℝ-refl {embedℚ dv})

    ch7 : (X *ℝ Q +ℝ embedℚ (dv * Nq)) +ℝ embedℚ dv
        ≈ℝ X *ℝ Q +ℝ embedℚ ((dv * Nq) + dv)
    ch7 = ≈ℝ-trans (+ℝ-assoc (X *ℝ Q) (embedℚ (dv * Nq)) (embedℚ dv))
            (+ℝ-cong (≈ℝ-refl {X *ℝ Q}) (≈ℝ-sym (embedℚ-+ (dv * Nq) dv)))

    ch8 : X *ℝ Q +ℝ embedℚ ((dv * Nq) + dv) ≤ℝ X *ℝ Q +ℝ embedℚ e
    ch8 = ≤ℝ-+-monoˡ {embedℚ ((dv * Nq) + dv)} {embedℚ e} {X *ℝ Q}
            (embedℚ-≤ ((dv * Nq) + dv) e bud')

    le-part : Cx ≤ℝ X *ℝ Q +ℝ embedℚ e
    le-part = ≤ℝ-trans ch1
                (≤ℝ-trans ch2
                  (≤ℝ-trans ch3
                    (≤ℝ-trans ch4
                      (≤ℝ-trans ch5
                        (≤ℝ-trans (≈⇒≤ℝ ch6)
                          (≤ℝ-trans (≈⇒≤ℝ ch7) ch8))))))

  in
    le-part

------------------------------------------------------------------------
-- The upper half at one window endpoint
--
-- 一个窗端点处的上界

-- The same window supplies the upper half, together with the product
-- comparison that bounds the second factor.
--
-- 同一扇窗给出上界，并附上界住第二个因子的乘积比较。
expℝ-add-shift-tail-ge :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
    (e : ℚ) (0<e : 0ℚ < e)
    (hh : ℚ) (0<hh : 0ℚ < hh) (0≤hh : 0ℚ ≤ hh) (hh≤1 : hh ≤ 1ℚ)
    (p : ℚ) (0≤p : 0ℚ ≤ p) (p≤x : embedℚ p ≤ℝ x)
    (x≤ph : x ≤ℝ embedℚ (p + hh))
    (U₀ : ℚ) (B : ℚ) (0≤B : 0ℚ ≤ B)
    (bndU : (j : ℕ) → expPartial (U₀ + q) j ≤ B)
    (Nq : ℚ) (0≤Nq : 0ℚ ≤ Nq)
    (Q≤Nq : expℝ (embedℚ q) (embed-nonNeg q 0≤q) ≤ℝ embedℚ Nq)
    (p1<U₀ : p + 1ℚ < U₀)
    (bud' : (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e)  → (expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q))
    ≤ℝ expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q) +ℝ embedℚ e
expℝ-add-shift-tail-ge x 0≤x q 0≤q e 0<e hh 0<hh 0≤hh hh≤1 p 0≤p p≤x x≤ph
    U₀ B 0≤B bndU Nq 0≤Nq Q≤Nq p1<U₀ bud' =
  let
    eq : RealI
    eq = embedℚ q

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    xq : RealI
    xq = x +ℝ eq

    0≤xq : 0ℝ ≤ℝ xq
    0≤xq = 0≤shift x 0≤x q 0≤q

    X : RealI
    X = expℝ x 0≤x

    Q : RealI
    Q = expℝ eq 0≤eq

    0≤Q : 0ℝ ≤ℝ Q
    0≤Q = expℝ-nonNeg eq 0≤eq

    Cx : RealI
    Cx = expℝ xq 0≤xq

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤ph : 0ℚ ≤ p + hh
    0≤ph = ≤-trans 0≤p (le-add-right p hh 0≤hh)

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)

    0≤pqh : 0ℚ ≤ (p + q) + hh
    0≤pqh = ≤-trans 0≤pq (le-add-right (p + q) hh 0≤hh)

    ph≤p1 : p + hh ≤ p + 1ℚ
    ph≤p1 = +-mono-≤ (≤-refl {p}) hh≤1

    ph≤U₀ : p + hh ≤ U₀
    ph≤U₀ = ≤-trans ph≤p1 (<⇒≤ p1<U₀)

    ph≤U : p + hh ≤ U₀ + q
    ph≤U = ≤-trans ph≤U₀ (le-add-right U₀ q 0≤q)

    re₀ : (p + q) + hh ≡ p + (q + hh)
    re₀ = +-assoc p q hh

    re₁ : p + (q + hh) ≡ p + (hh + q)
    re₁ = cong (λ z → p + z) (+-comm q hh)

    re₂ : p + (hh + q) ≡ (p + hh) + q
    re₂ = sym (+-assoc p hh q)

    re : (p + q) + hh ≡ (p + hh) + q
    re = trans re₀ (trans re₁ re₂)

    pqh≤phq : (p + q) + hh ≤ (p + hh) + q
    pqh≤phq = ≤-reflexive re

    phq≤Uq : (p + hh) + q ≤ U₀ + q
    phq≤Uq = +-mono-≤ ph≤U₀ (≤-refl {q})

    pqh≤U : (p + q) + hh ≤ U₀ + q
    pqh≤U = ≤-trans pqh≤phq phq≤Uq

    bnd₀ : (j : ℕ) → expPartial (p + hh) j ≤ B
    bnd₀ j = ≤-trans (expPartial-le-param (p + hh) (U₀ + q) 0≤ph ph≤U j) (bndU j)

    bnd₁ : (j : ℕ) → expPartial ((p + q) + hh) j ≤ B
    bnd₁ j = ≤-trans (expPartial-le-param ((p + q) + hh) (U₀ + q) 0≤pqh pqh≤U j)
               (bndU j)

    ep₀ : RealI
    ep₀ = embedℚ p

    0≤ep₀ : 0ℝ ≤ℝ ep₀
    0≤ep₀ = embed-nonNeg p 0≤p

    ep : RealI
    ep = expℝ ep₀ 0≤ep₀

    ep≤ph : embedℚ p ≤ℝ embedℚ (p + hh)
    ep≤ph = embedℚ-≤ p (p + hh) (le-add-right p hh 0≤hh)

    cX : Close (hh * (1ℚ + B) + hh) X ep
    cX = expℝ-close-window p hh 0≤p 0≤hh B bnd₀ hh 0<hh x ep₀ 0≤x 0≤ep₀
           p≤x x≤ph (≤ℝ-refl {ep₀}) ep≤ph

    pq≤xq₀ : embedℚ p +ℝ embedℚ q ≤ℝ x +ℝ embedℚ q
    pq≤xq₀ = ≤ℝ-+-mono {embedℚ p} {x} {embedℚ q} p≤x

    pq≈ : embedℚ (p + q) ≈ℝ embedℚ p +ℝ embedℚ q
    pq≈ = embedℚ-+ p q

    epq : RealI
    epq = embedℚ (p + q)

    0≤epq : 0ℝ ≤ℝ epq
    0≤epq = embed-nonNeg (p + q) 0≤pq

    pq≤xq : epq ≤ℝ xq
    pq≤xq = ≤ℝ-resp-≈ (≈ℝ-sym pq≈) (≈ℝ-refl {xq}) pq≤xq₀

    xq≤phq₀ : x +ℝ embedℚ q ≤ℝ embedℚ (p + hh) +ℝ embedℚ q
    xq≤phq₀ = ≤ℝ-+-mono {x} {embedℚ (p + hh)} {embedℚ q} x≤ph

    phq≈ : embedℚ (p + hh) +ℝ embedℚ q ≈ℝ embedℚ ((p + hh) + q)
    phq≈ = ≈ℝ-sym (embedℚ-+ (p + hh) q)

    xq≤phq : xq ≤ℝ embedℚ ((p + hh) + q)
    xq≤phq = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) phq≈ xq≤phq₀

    xq≤pqh : xq ≤ℝ embedℚ ((p + q) + hh)
    xq≤pqh = ≤ℝ-resp-≈ (≈ℝ-refl {xq}) (embedℚ-cong (sym re)) xq≤phq

    epq≤pqh : embedℚ (p + q) ≤ℝ embedℚ ((p + q) + hh)
    epq≤pqh = embedℚ-≤ (p + q) ((p + q) + hh)
                (le-add-right (p + q) hh 0≤hh)

    PQ : RealI
    PQ = expℝ epq 0≤epq

    cC : Close (hh * (1ℚ + B) + hh) Cx PQ
    cC = expℝ-close-window (p + q) hh 0≤pq 0≤hh B bnd₁ hh 0<hh xq epq 0≤xq 0≤epq
           pq≤xq xq≤pqh (≤ℝ-refl {epq}) epq≤pqh

    dv : ℚ
    dv = hh * (1ℚ + B) + hh

    0≤dv : 0ℚ ≤ dv
    0≤dv = ≤-trans (prod-nonNeg hh (1ℚ + B) 0≤hh 0≤1B)
             (le-add-right (hh * (1ℚ + B)) hh 0≤hh)

    0≤edv : 0ℝ ≤ℝ embedℚ dv
    0≤edv = embed-nonNeg dv 0≤dv

    -- The two components of the first window.
    --
    -- 第一个窗口的两个分量。
    X<Pdv : X <ℝ ep +ℝ embedℚ dv
    X<Pdv = ≈-<-resp (sub-add-cancelℝ X (embedℚ dv))
              (<-+mono (X -ℝ embedℚ dv) ep (embedℚ dv) (proj₁ cX))

    X≤Pdv : X ≤ℝ ep +ℝ embedℚ dv
    X≤Pdv = <⇒≤ℝ X<Pdv

    PQ≤Cdv : PQ ≤ℝ Cx +ℝ embedℚ dv
    PQ≤Cdv = <⇒≤ℝ (proj₂ cC)

    -- The rational additivity law at the two window endpoints.
    --
    -- 两个窗口端点处的有理加法律。
    rat : PQ ≈ℝ ep *ℝ Q
    rat = expℝ-add-rat p q 0≤p 0≤q

    -- The two rational products with the exponential at `q`.
    --
    -- 与 `q` 处指数相乘的两个有理积。
    dQ≤dNq : embedℚ dv *ℝ Q ≤ℝ embedℚ dv *ℝ embedℚ Nq
    dQ≤dNq = ≤ℝ-resp-≈ (*ℝ-comm Q (embedℚ dv))
              (*ℝ-comm (embedℚ Nq) (embedℚ dv))
              (*ℝ-≤-mono Q (embedℚ Nq) (embedℚ dv) Q≤Nq 0≤edv)

    -- The upper estimate `X * Q ≤ C + e`.
    --
    -- 上界估计 `X * Q ≤ C + e`。
    g1 : X *ℝ Q ≤ℝ (ep +ℝ embedℚ dv) *ℝ Q
    g1 = *ℝ-≤-mono X (ep +ℝ embedℚ dv) Q X≤Pdv 0≤Q

    g2 : (ep +ℝ embedℚ dv) *ℝ Q ≈ℝ ep *ℝ Q +ℝ embedℚ dv *ℝ Q
    g2 = *ℝ-distribʳ-+ Q ep (embedℚ dv)

    g3 : ep *ℝ Q +ℝ embedℚ dv *ℝ Q ≤ℝ PQ +ℝ embedℚ dv *ℝ Q
    g3 = ≤ℝ-+-mono {ep *ℝ Q} {PQ} {embedℚ dv *ℝ Q}
           (≈⇒≤ℝ (≈ℝ-sym rat))

    g4 : PQ +ℝ embedℚ dv *ℝ Q ≤ℝ (Cx +ℝ embedℚ dv) +ℝ embedℚ dv *ℝ Q
    g4 = ≤ℝ-+-mono {PQ} {Cx +ℝ embedℚ dv} {embedℚ dv *ℝ Q} PQ≤Cdv

    g5 : (Cx +ℝ embedℚ dv) +ℝ embedℚ dv *ℝ Q
        ≈ℝ Cx +ℝ (embedℚ dv +ℝ embedℚ dv *ℝ Q)
    g5 = +ℝ-assoc Cx (embedℚ dv) (embedℚ dv *ℝ Q)

    g6 : Cx +ℝ (embedℚ dv +ℝ embedℚ dv *ℝ Q)
        ≈ℝ Cx +ℝ (embedℚ dv *ℝ Q +ℝ embedℚ dv)
    g6 = +ℝ-cong (≈ℝ-refl {Cx}) (+ℝ-comm (embedℚ dv) (embedℚ dv *ℝ Q))

    g7 : Cx +ℝ (embedℚ dv *ℝ Q +ℝ embedℚ dv)
        ≤ℝ Cx +ℝ (embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv)
    g7 = ≤ℝ-+-monoˡ {embedℚ dv *ℝ Q +ℝ embedℚ dv}
            {embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv} {Cx}
            (≤ℝ-+-mono {embedℚ dv *ℝ Q} {embedℚ dv *ℝ embedℚ Nq} {embedℚ dv} dQ≤dNq)

    g8 : Cx +ℝ (embedℚ dv *ℝ embedℚ Nq +ℝ embedℚ dv)
        ≈ℝ Cx +ℝ (embedℚ (dv * Nq) +ℝ embedℚ dv)
    g8 = +ℝ-cong (≈ℝ-refl {Cx})
           (+ℝ-cong (≈ℝ-sym (embedℚ-* dv Nq)) (≈ℝ-refl {embedℚ dv}))

    g9 : Cx +ℝ (embedℚ (dv * Nq) +ℝ embedℚ dv)
        ≈ℝ Cx +ℝ embedℚ ((dv * Nq) + dv)
    g9 = +ℝ-cong (≈ℝ-refl {Cx}) (≈ℝ-sym (embedℚ-+ (dv * Nq) dv))

    g10 : Cx +ℝ embedℚ ((dv * Nq) + dv) ≤ℝ Cx +ℝ embedℚ e
    g10 = ≤ℝ-+-monoˡ {embedℚ ((dv * Nq) + dv)} {embedℚ e} {Cx}
            (embedℚ-≤ ((dv * Nq) + dv) e bud')

    ge-part : X *ℝ Q ≤ℝ Cx +ℝ embedℚ e
    ge-part = ≤ℝ-trans g1
                (≤ℝ-trans (≈⇒≤ℝ g2)
                  (≤ℝ-trans g3
                    (≤ℝ-trans g4
                      (≤ℝ-trans (≈⇒≤ℝ g5)
                        (≤ℝ-trans (≈⇒≤ℝ g6)
                          (≤ℝ-trans g7
                            (≤ℝ-trans (≈⇒≤ℝ g8)
                              (≤ℝ-trans (≈⇒≤ℝ g9) g10))))))))
  in
    ge-part

------------------------------------------------------------------------
-- The budget inequality in symbolic form
--
-- 符号形式的预算不等式

-- The width, the bound and the natural bound stay variables, so no rational
-- arithmetic is ever evaluated at concrete values.
--
-- 窗宽、界与自然界都保持为变量，因而有理算术不会在具体值上求值。
exp-add-shift-budget :
    (hh B Nq e : ℚ)
  → hh * (((1ℚ + B) + 1ℚ) * (1ℚ + Nq)) < e
  → (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e
exp-add-shift-budget hh B Nq e lt =
  let
    a : ℚ
    a = hh * (1ℚ + B)

    u : ℚ
    u = hh * ((1ℚ + B) + 1ℚ)

    step₁ : a + hh ≡ u
    step₁ = trans (cong (λ z → a + z) (sym (*-identityʳ hh)))
             (sym (*-distribˡ-+ hh (1ℚ + B) 1ℚ))

    step₂ : (a + hh) * Nq + (a + hh) ≡ u * Nq + u
    step₂ = cong₂ (λ z w → z + w) (cong (λ z → z * Nq) step₁) step₁

    step₃ : u * Nq + u ≡ u * (Nq + 1ℚ)
    step₃ = trans (cong (λ z → u * Nq + z) (sym (*-identityʳ u)))
             (sym (*-distribˡ-+ u Nq 1ℚ))

    step₄ : u * (Nq + 1ℚ) ≡ hh * (((1ℚ + B) + 1ℚ) * (1ℚ + Nq))
    step₄ = trans (cong (λ z → u * z) (+-comm Nq 1ℚ))
             (*-assoc hh ((1ℚ + B) + 1ℚ) (1ℚ + Nq))

    total : (a + hh) * Nq + (a + hh)
          ≡ hh * (((1ℚ + B) + 1ℚ) * (1ℚ + Nq))
    total = trans step₂ (trans step₃ step₄)
  in
    ≤-trans (≤-reflexive total) (<⇒≤ lt)

------------------------------------------------------------------------
-- The two halves at real points
--
-- 实数点处的两半

-- Each half is obtained from the budgeted estimate by an arbitrarily
-- small rational slack, with the window supplied once per half.
--
-- 每一半都由带预算的估计经任意小有理余量得到，窗在每一半中各自给出。
expℝ-add-shift-le :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
  → expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q)
    ≤ℝ expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expℝ-add-shift-le x 0≤x q 0≤q =
  ≤ℝ-of-slack (expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q))
    (expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q))
    (λ e 0<e →
  let
    eq : RealI
    eq = embedℚ q

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    Q : RealI
    Q = expℝ eq 0≤eq

    -- A rational strictly above `x + 1`.
    --
    -- 严格高于 `x + 1` 的一个有理点。
    x1 : RealI
    x1 = x +ℝ embedℚ 1ℚ

    0≤x1 : 0ℝ ≤ℝ x1
    0≤x1 = 0≤shift x 0≤x 1ℚ (<⇒≤ 0<1)

    x1<x1p1 : x1 <ℝ x1 +ℝ embedℚ 1ℚ
    x1<x1p1 = ≈-<-respʳ (+ℝ-comm (embedℚ 1ℚ) x1)
                (≈-<-resp (+ℝ-identityˡ x1)
                  (<-+mono 0ℝ (embedℚ 1ℚ) x1 (0<embedℚ 1ℚ 0<1)))

    up : Σ ℚ (λ t → (x1 <ℝ embedℚ t) × (embedℚ t <ℝ x1 +ℝ embedℚ 1ℚ))
    up = dense {x1} {x1 +ℝ embedℚ 1ℚ} x1<x1p1

    U₀ : ℚ
    U₀ = proj₁ up

    x1<U₀ : x1 <ℝ embedℚ U₀
    x1<U₀ = proj₁ (proj₂ up)

    0≤U₀ : 0ℚ ≤ U₀
    0≤U₀ = <⇒≤ (embedℚ-reflect 0ℚ U₀ (≤ℝ-<trans 0≤x1 x1<U₀))

    U : ℚ
    U = U₀ + q

    0≤U : 0ℚ ≤ U
    0≤U = ≤-trans 0≤U₀ (le-add-right U₀ q 0≤q)

    ub : Σ ℚ (λ B → (j : ℕ) → expPartial U j ≤ B)
    ub = expPartial-bound U 0≤U 1ℚ 0<1

    B : ℚ
    B = proj₁ ub

    bndU : (j : ℕ) → expPartial U j ≤ B
    bndU = proj₂ ub

    0≤B : 0ℚ ≤ B
    0≤B = subst (λ z → z ≤ B) (expPartial-zero U) (bndU zero)

    -- A rational bound for the exponential at `q`.
    --
    -- `q` 处指数的一个有理上界。
    nb : Σ ℕ (λ N → Q ≤ℝ embedℚ (embed (suc N)))
    nb = expℝ-bound-nat eq 0≤eq (q + 1ℚ)
           (≤-trans 0≤q (le-add-right q 1ℚ (<⇒≤ 0<1)))
           (embedℚ-≤ q (q + 1ℚ) (le-add-right q 1ℚ (<⇒≤ 0<1))) 1ℚ 0<1

    Nqb : ℕ
    Nqb = proj₁ nb

    Nq : ℚ
    Nq = embed (suc Nqb)

    Q≤Nq : Q ≤ℝ embedℚ Nq
    Q≤Nq = proj₂ nb

    0≤Nq : 0ℚ ≤ Nq
    0≤Nq = <⇒≤ (0<embed Nqb)

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤1Nq : 0ℚ ≤ 1ℚ + Nq
    0≤1Nq = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ Nq 0≤Nq)

    0≤cL : 0ℚ ≤ (1ℚ + B) + 1ℚ
    0≤cL = ≤-trans 0≤1B (le-add-right (1ℚ + B) 1ℚ (<⇒≤ 0<1))

    cc : ℚ
    cc = ((1ℚ + B) + 1ℚ) * (1ℚ + Nq)

    0≤cc : 0ℚ ≤ cc
    0≤cc = prod-nonNeg ((1ℚ + B) + 1ℚ) (1ℚ + Nq) 0≤cL 0≤1Nq

    sh : Σ ℕ (λ j → ε j * cc < e)
    sh = rat-shrink cc 0≤cc e 0<e

    jj : ℕ
    jj = proj₁ sh

    shr : ε jj * cc < e
    shr = proj₂ sh

    -- the width is a single precision, so the budget carries no doubling
    -- arithmetic
    --
    -- 窗宽取单个精度，预算中因而没有加倍算术。
    hh : ℚ
    hh = ε jj

    0<hh : 0ℚ < hh
    0<hh = 0<ε jj

    0≤hh : 0ℚ ≤ hh
    0≤hh = <⇒≤ 0<hh

    hh≤1 : hh ≤ 1ℚ
    hh≤1 = ε-≤-1 jj

    win : Σ ℚ (λ p → (0ℚ ≤ p)
                 × (embedℚ p ≤ℝ x × x ≤ℝ embedℚ (p + hh)))
    win = rat-window-nonNeg x 0≤x hh 0<hh

    p : ℚ
    p = proj₁ win

    0≤p : 0ℚ ≤ p
    0≤p = proj₁ (proj₂ win)

    p≤x : embedℚ p ≤ℝ x
    p≤x = proj₁ (proj₂ (proj₂ win))

    x≤ph : x ≤ℝ embedℚ (p + hh)
    x≤ph = proj₂ (proj₂ (proj₂ win))

    -- The right endpoint stays inside the bound point.
    --
    -- 右端点仍在受界点之内。
    embp1≈ : embedℚ p +ℝ embedℚ 1ℚ ≈ℝ embedℚ (p + 1ℚ)
    embp1≈ = ≈ℝ-sym (embedℚ-+ p 1ℚ)

    embp≤x1 : embedℚ p +ℝ embedℚ 1ℚ ≤ℝ x +ℝ embedℚ 1ℚ
    embp≤x1 = ≤ℝ-+-mono {embedℚ p} {x} {embedℚ 1ℚ} p≤x

    embp1≤x1 : embedℚ (p + 1ℚ) ≤ℝ x +ℝ embedℚ 1ℚ
    embp1≤x1 = ≤ℝ-resp-≈ embp1≈ (≈ℝ-refl {x +ℝ embedℚ 1ℚ}) embp≤x1

    embp1<U₀ : embedℚ (p + 1ℚ) <ℝ embedℚ U₀
    embp1<U₀ = ≤ℝ-<trans embp1≤x1 x1<U₀

    p1<U₀ : p + 1ℚ < U₀
    p1<U₀ = embedℚ-reflect (p + 1ℚ) U₀ embp1<U₀

    -- The budget is the tolerance lifted out of the product.
    --
    -- 预算即从乘积中提出来的容差。
    bud' : (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e
    bud' = exp-add-shift-budget hh B Nq e shr

  in
    expℝ-add-shift-tail-le x 0≤x q 0≤q e 0<e hh 0<hh 0≤hh hh≤1
      p 0≤p p≤x x≤ph U₀ B 0≤B bndU Nq 0≤Nq Q≤Nq p1<U₀ bud')

expℝ-add-shift-ge :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
  → expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
    ≤ℝ expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q)
expℝ-add-shift-ge x 0≤x q 0≤q =
  ≤ℝ-of-slack (expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q))
    (expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q))
    (λ e 0<e →
  let
    eq : RealI
    eq = embedℚ q

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    Q : RealI
    Q = expℝ eq 0≤eq

    -- A rational strictly above `x + 1`.
    --
    -- 严格高于 `x + 1` 的一个有理点。
    x1 : RealI
    x1 = x +ℝ embedℚ 1ℚ

    0≤x1 : 0ℝ ≤ℝ x1
    0≤x1 = 0≤shift x 0≤x 1ℚ (<⇒≤ 0<1)

    x1<x1p1 : x1 <ℝ x1 +ℝ embedℚ 1ℚ
    x1<x1p1 = ≈-<-respʳ (+ℝ-comm (embedℚ 1ℚ) x1)
                (≈-<-resp (+ℝ-identityˡ x1)
                  (<-+mono 0ℝ (embedℚ 1ℚ) x1 (0<embedℚ 1ℚ 0<1)))

    up : Σ ℚ (λ t → (x1 <ℝ embedℚ t) × (embedℚ t <ℝ x1 +ℝ embedℚ 1ℚ))
    up = dense {x1} {x1 +ℝ embedℚ 1ℚ} x1<x1p1

    U₀ : ℚ
    U₀ = proj₁ up

    x1<U₀ : x1 <ℝ embedℚ U₀
    x1<U₀ = proj₁ (proj₂ up)

    0≤U₀ : 0ℚ ≤ U₀
    0≤U₀ = <⇒≤ (embedℚ-reflect 0ℚ U₀ (≤ℝ-<trans 0≤x1 x1<U₀))

    U : ℚ
    U = U₀ + q

    0≤U : 0ℚ ≤ U
    0≤U = ≤-trans 0≤U₀ (le-add-right U₀ q 0≤q)

    ub : Σ ℚ (λ B → (j : ℕ) → expPartial U j ≤ B)
    ub = expPartial-bound U 0≤U 1ℚ 0<1

    B : ℚ
    B = proj₁ ub

    bndU : (j : ℕ) → expPartial U j ≤ B
    bndU = proj₂ ub

    0≤B : 0ℚ ≤ B
    0≤B = subst (λ z → z ≤ B) (expPartial-zero U) (bndU zero)

    -- A rational bound for the exponential at `q`.
    --
    -- `q` 处指数的一个有理上界。
    nb : Σ ℕ (λ N → Q ≤ℝ embedℚ (embed (suc N)))
    nb = expℝ-bound-nat eq 0≤eq (q + 1ℚ)
           (≤-trans 0≤q (le-add-right q 1ℚ (<⇒≤ 0<1)))
           (embedℚ-≤ q (q + 1ℚ) (le-add-right q 1ℚ (<⇒≤ 0<1))) 1ℚ 0<1

    Nqb : ℕ
    Nqb = proj₁ nb

    Nq : ℚ
    Nq = embed (suc Nqb)

    Q≤Nq : Q ≤ℝ embedℚ Nq
    Q≤Nq = proj₂ nb

    0≤Nq : 0ℚ ≤ Nq
    0≤Nq = <⇒≤ (0<embed Nqb)

    0≤1B : 0ℚ ≤ 1ℚ + B
    0≤1B = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ B 0≤B)

    0≤1Nq : 0ℚ ≤ 1ℚ + Nq
    0≤1Nq = ≤-trans (<⇒≤ 0<1) (le-add-right 1ℚ Nq 0≤Nq)

    0≤cL : 0ℚ ≤ (1ℚ + B) + 1ℚ
    0≤cL = ≤-trans 0≤1B (le-add-right (1ℚ + B) 1ℚ (<⇒≤ 0<1))

    cc : ℚ
    cc = ((1ℚ + B) + 1ℚ) * (1ℚ + Nq)

    0≤cc : 0ℚ ≤ cc
    0≤cc = prod-nonNeg ((1ℚ + B) + 1ℚ) (1ℚ + Nq) 0≤cL 0≤1Nq

    sh : Σ ℕ (λ j → ε j * cc < e)
    sh = rat-shrink cc 0≤cc e 0<e

    jj : ℕ
    jj = proj₁ sh

    shr : ε jj * cc < e
    shr = proj₂ sh

    -- the width is a single precision, so the budget carries no doubling
    -- arithmetic
    --
    -- 窗宽取单个精度，预算中因而没有加倍算术。
    hh : ℚ
    hh = ε jj

    0<hh : 0ℚ < hh
    0<hh = 0<ε jj

    0≤hh : 0ℚ ≤ hh
    0≤hh = <⇒≤ 0<hh

    hh≤1 : hh ≤ 1ℚ
    hh≤1 = ε-≤-1 jj

    win : Σ ℚ (λ p → (0ℚ ≤ p)
                 × (embedℚ p ≤ℝ x × x ≤ℝ embedℚ (p + hh)))
    win = rat-window-nonNeg x 0≤x hh 0<hh

    p : ℚ
    p = proj₁ win

    0≤p : 0ℚ ≤ p
    0≤p = proj₁ (proj₂ win)

    p≤x : embedℚ p ≤ℝ x
    p≤x = proj₁ (proj₂ (proj₂ win))

    x≤ph : x ≤ℝ embedℚ (p + hh)
    x≤ph = proj₂ (proj₂ (proj₂ win))

    -- The right endpoint stays inside the bound point.
    --
    -- 右端点仍在受界点之内。
    embp1≈ : embedℚ p +ℝ embedℚ 1ℚ ≈ℝ embedℚ (p + 1ℚ)
    embp1≈ = ≈ℝ-sym (embedℚ-+ p 1ℚ)

    embp≤x1 : embedℚ p +ℝ embedℚ 1ℚ ≤ℝ x +ℝ embedℚ 1ℚ
    embp≤x1 = ≤ℝ-+-mono {embedℚ p} {x} {embedℚ 1ℚ} p≤x

    embp1≤x1 : embedℚ (p + 1ℚ) ≤ℝ x +ℝ embedℚ 1ℚ
    embp1≤x1 = ≤ℝ-resp-≈ embp1≈ (≈ℝ-refl {x +ℝ embedℚ 1ℚ}) embp≤x1

    embp1<U₀ : embedℚ (p + 1ℚ) <ℝ embedℚ U₀
    embp1<U₀ = ≤ℝ-<trans embp1≤x1 x1<U₀

    p1<U₀ : p + 1ℚ < U₀
    p1<U₀ = embedℚ-reflect (p + 1ℚ) U₀ embp1<U₀

    -- The budget is the tolerance lifted out of the product.
    --
    -- 预算即从乘积中提出来的容差。
    bud' : (hh * (1ℚ + B) + hh) * Nq + (hh * (1ℚ + B) + hh) ≤ e
    bud' = exp-add-shift-budget hh B Nq e shr

  in
    expℝ-add-shift-tail-ge x 0≤x q 0≤q e 0<e hh 0<hh 0≤hh hh≤1
      p 0≤p p≤x x≤ph U₀ B 0≤B bndU Nq 0≤Nq Q≤Nq p1<U₀ bud')

------------------------------------------------------------------------
-- Additivity at real points with a rational summand
--
-- 实数点加有理加元的可加性

-- The two halves are joined by antisymmetry.
--
-- 两个半支由反对称性合拢。
expℝ-add-shift :
    (x : RealI) (0≤x : 0ℝ ≤ℝ x) (q : ℚ) (0≤q : 0ℚ ≤ q)
  → expℝ (x +ℝ embedℚ q) (0≤shift x 0≤x q 0≤q)
    ≈ℝ expℝ x 0≤x *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expℝ-add-shift x 0≤x q 0≤q =
  ≤ℝ-antisym (expℝ-add-shift-le x 0≤x q 0≤q)
    (expℝ-add-shift-ge x 0≤x q 0≤q)

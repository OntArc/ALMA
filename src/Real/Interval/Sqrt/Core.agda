------------------------------------------------------------------------
-- The square root as a supremum
--
-- 平方根作为上确界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Sqrt.Core where

open import Data.Nat using (ℕ; suc; s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties as Nat using (n<1+n)
  renaming (<-trans to <-transℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _*_; _<_; positive)
open import Data.Rational.Properties as ℚP using (*-monoˡ-<-pos; *-identityˡ)
open import Relation.Binary.PropositionalEquality using (subst)

open import Real using (embed; 0<embed; embed-mono-<)
open import Real.IntervalEquiv using (width)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (0<embedℚ; embedℚ-mono)
open import Real.Interval.DensityArch using (archimedean)
open import Real.Interval.Embed using (embedℚ-*)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using (*ℝ-comm)
open import Real.Interval.Mul.Order using (<-*mono; ≈-<-respʳ)
open import Real.Interval.Order using (_<ℝ_; <-trans; <-irrefl)
open import Real.Interval.OrderLaws using (width-below-strict)
open import Real.Interval.OrderComplete using (sup; sup-upper; sup-least)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Sqrt.Located using (P; P-0; located)

module _ (y : RealI) (0<y : 0ℝ <ℝ y) where

  ----------------------------------------------------------------------
  -- A rational squared bound above y
  --
  -- 高于 y 的有理平方上界

  -- sqrtℝ y is the least upper bound of the located set
  -- P x = (0 ≤ x) × (x * x < y). The upper bound fed to the order-complete
  -- interface is a rational q with 1 < q and y < q * q, so every member
  -- of P lies below q. Existence of such a q is the archimedean property.
  --
  -- sqrtℝ y 是定位集 P x = (0 ≤ x) × (x * x < y) 的最小上界。喂给序
  -- 完备接口的上界是满足 1 < q 且 y < q * q 的有理数 q，故 P 的每个
  -- 成员都低于 q。这样的 q 存在即阿基米德性质。
  n : ℕ
  n = proj₁ (archimedean y)

  n<suc-suc : n <ℕ suc (suc n)
  n<suc-suc = <-transℕ (n<1+n n) (n<1+n (suc n))

  q : ℚ
  q = embed (suc (suc n))

  0<q : 0ℚ < q
  0<q = 0<embed (suc n)

  1<q : 1ℚ < q
  1<q = embed-mono-< {1} {suc (suc n)} (s≤s (s≤s z≤n))

  y<eq : y <ℝ embedℚ q
  y<eq = <-trans
    (proj₂ (archimedean y))
    (embedℚ-mono (embed n) q
      (embed-mono-< {n} {suc (suc n)} n<suc-suc))

  q<qq : q < q * q
  q<qq = subst (λ z → z < q * q) (*-identityˡ q)
    (*-monoˡ-<-pos q {{positive 0<q}} 1<q)

  y<eqq : y <ℝ embedℚ (q * q)
  y<eqq = <-trans y<eq (embedℚ-mono q (q * q) q<qq)

  ----------------------------------------------------------------------
  -- The candidate upper bound
  --
  -- 候选上界

  rq : RealI
  rq = embedℚ q

  ----------------------------------------------------------------------
  -- Every member of P is below rq
  --
  -- P 的每个成员都低于 rq

  isUpper : (x : RealI) → P y 0<y x → x ≤ℝ rq
  isUpper x px rq<x =
    let
      xx<y : x *ℝ x <ℝ y
      xx<y = proj₂ px

      0<rq : 0ℝ <ℝ rq
      0<rq = 0<embedℚ q 0<q

      0<x : 0ℝ <ℝ x
      0<x = <-trans 0<rq rq<x

      rq²<rqx : rq *ℝ rq <ℝ rq *ℝ x
      rq²<rqx = ≈-<-respʳ (*ℝ-comm x rq)
        (<-*mono rq x rq rq<x 0<rq)

      rqx<x² : rq *ℝ x <ℝ x *ℝ x
      rqx<x² = <-*mono rq x x rq<x 0<x

      rq²<x² : rq *ℝ rq <ℝ x *ℝ x
      rq²<x² = <-trans rq²<rqx rqx<x²

      y<rq² : y <ℝ rq *ℝ rq
      y<rq² = ≈-<-respʳ (embedℚ-* q q) y<eqq

      rq²<rq² : rq *ℝ rq <ℝ rq *ℝ rq
      rq²<rq² = <-trans rq²<x² (<-trans xx<y y<rq²)
    in
      <-irrefl (rq *ℝ rq) rq²<rq²

  ----------------------------------------------------------------------
  -- The square root
  --
  -- 平方根

  sqrtℝ : RealI
  sqrtℝ = sup {P = P y 0<y} (located y 0<y) {x₀ = 0ℝ}
              (P-0 y 0<y) {u₀ = rq} isUpper

  sqrt-upper : (x : RealI) → P y 0<y x → x ≤ℝ sqrtℝ
  sqrt-upper = sup-upper {P = P y 0<y} (located y 0<y) {x₀ = 0ℝ}
                 (P-0 y 0<y) {u₀ = rq} isUpper

  sqrt-least : (u : RealI) → ((x : RealI) → P y 0<y x → x ≤ℝ u)
             → sqrtℝ ≤ℝ u
  sqrt-least = sup-least {P = P y 0<y} (located y 0<y) {x₀ = 0ℝ}
                 (P-0 y 0<y) {u₀ = rq} isUpper

  sqrt-nonNeg : 0ℝ ≤ℝ sqrtℝ
  sqrt-nonNeg = sqrt-upper 0ℝ (P-0 y 0<y)

  ----------------------------------------------------------------------
  -- Bracket width of the square root
  --
  -- 平方根的括号宽度

  -- The brackets that compute sqrtℝ have arbitrarily small width, so the
  -- radical is pinned down to any rational accuracy. The two-sided
  -- enclosure itself is l-layer-≤ / u-layer-≤ in Sqrt.Bounds applied to
  -- sqrtℝ, combined with l-sup / u-sup from OrderComplete.
  --
  -- 计算 sqrtℝ 的括号宽度任意小，故根可被任何有理精度夹定。两侧的
  -- 夹持即 Sqrt.Bounds 的 l-layer-≤ / u-layer-≤ 用在 sqrtℝ 上，再配
  -- OrderComplete 的 l-sup / u-sup。
  bracket-width : (b : ℚ) → 0ℚ < b → Σ ℕ (λ m → width sqrtℝ m < b)
  bracket-width b 0<b =
    let
      sel = width-below-strict sqrtℝ b 0 0<b
      m = proj₁ sel
      h = proj₂ (proj₂ sel)
    in
      m , h

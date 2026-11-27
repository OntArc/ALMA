------------------------------------------------------------------------
-- Order laws for the reciprocal on interval reals
--
-- 区间实数上倒数的序律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.RecipOrder where

open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Inverse using (*ℝ-inverse-pos)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Laws using (*ℝ-comm; *ℝ-assoc; *ℝ-identityˡ)
open import Real.Interval.Mul.Order using
  (*ℝ-≤-mono; <-*mono; ≈-<-respʳ; ≤-resp-≈ˡ; ≤-resp-≈ʳ)
open import Real.Interval.Order using (_<ℝ_; <-irrefl)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.OrderLe using (<-≤ℝ-trans; <⇒≤ℝ)
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using (recipℝ-pos; recipℝ-1; recipℝ-cong)

------------------------------------------------------------------------
-- One as the product of a positive real with its reciprocal
--
-- 一作为正实数与其倒数之积

inv-left : (x : RealI) (0<x : 0ℝ <ℝ x) → 1ℝ ≈ℝ recipℝ x 0<x *ℝ x
inv-left x 0<x =
  ≈ℝ-trans (≈ℝ-sym (*ℝ-inverse-pos x 0<x)) (*ℝ-comm x (recipℝ x 0<x))

inv-right : (x : RealI) (0<x : 0ℝ <ℝ x) → recipℝ x 0<x *ℝ x ≈ℝ 1ℝ
inv-right x 0<x =
  ≈ℝ-trans (*ℝ-comm (recipℝ x 0<x) x) (*ℝ-inverse-pos x 0<x)

------------------------------------------------------------------------
-- Multiplication by a positive factor on the left
--
-- 左侧乘以正因子

mul-≤-comm : (a b z : RealI) (a≤b : a ≤ℝ b) (0<z : 0ℝ <ℝ z) →
  z *ℝ a ≤ℝ z *ℝ b
mul-≤-comm a b z a≤b 0<z =
  ≤-resp-≈ʳ
    (≤-resp-≈ˡ (*ℝ-comm a z) (*ℝ-≤-mono a b z a≤b (<⇒≤ℝ 0<z)))
    (*ℝ-comm b z)

------------------------------------------------------------------------
-- The reciprocity proof is independent of the positivity witness
--
-- 倒数的取值与正性证据无关

recipℝ-pos-irr : (x : RealI) (p p' : 0ℝ <ℝ x) →
  recipℝ x p ≈ℝ recipℝ x p'
recipℝ-pos-irr x p p' = recipℝ-cong x x p p' ≈ℝ-refl

------------------------------------------------------------------------
-- Antitonicity of the reciprocal
--
-- 倒数的反单调性

recipℝ-antitone-of : (x y : RealI) (0<x : 0ℝ <ℝ x) (0<y : 0ℝ <ℝ y)
                     (x≤y : x ≤ℝ y)
                   → recipℝ y 0<y ≤ℝ recipℝ x 0<x
recipℝ-antitone-of x y 0<x 0<y x≤y Rx<Ry =
  <-irrefl 1ℝ
    (≈-<-respʳ (inv-right y 0<y)
      (≈-<-resp (≈ℝ-sym (inv-left x 0<x))
        (<-≤ℝ-trans
          (<-*mono (recipℝ x 0<x) (recipℝ y 0<y) x Rx<Ry 0<x)
          (mul-≤-comm x y (recipℝ y 0<y) x≤y (recipℝ-pos y 0<y)))))

recipℝ-antitone : (x y : RealI) (0<x : 0ℝ <ℝ x) (x≤y : x ≤ℝ y) →
  recipℝ y (<-≤ℝ-trans 0<x x≤y) ≤ℝ recipℝ x 0<x
recipℝ-antitone x y 0<x x≤y =
  recipℝ-antitone-of x y 0<x (<-≤ℝ-trans 0<x x≤y) x≤y

------------------------------------------------------------------------
-- Corollary: the reciprocal of a real at least one is at most one
--
-- 推论：不小于一的实数其倒数不大于一

recipℝ-≤-1-of : (x : RealI) (0<x : 0ℝ <ℝ x) (1≤x : 1ℝ ≤ℝ x) →
  recipℝ x 0<x ≤ℝ 1ℝ
recipℝ-≤-1-of x 0<x 1≤x =
  ≤-resp-≈ʳ {x = recipℝ x 0<x}
    {y = recipℝ 1ℝ 0ℝ<ℝ1ℝ} {z = 1ℝ}
    (≤-resp-≈ˡ {x = recipℝ x (<-≤ℝ-trans 0ℝ<ℝ1ℝ 1≤x)}
      {y = recipℝ x 0<x} {z = recipℝ 1ℝ 0ℝ<ℝ1ℝ}
      (≈ℝ-sym (recipℝ-pos-irr x 0<x (<-≤ℝ-trans 0ℝ<ℝ1ℝ 1≤x)))
      (recipℝ-antitone 1ℝ x 0ℝ<ℝ1ℝ 1≤x))
    recipℝ-1

recipℝ-≤-1 : (x : RealI) (1≤x : 1ℝ ≤ℝ x) →
  recipℝ x (<-≤ℝ-trans 0ℝ<ℝ1ℝ 1≤x) ≤ℝ 1ℝ
recipℝ-≤-1 x 1≤x =
  ≤-resp-≈ʳ {x = recipℝ x (<-≤ℝ-trans 0ℝ<ℝ1ℝ 1≤x)}
    {y = recipℝ 1ℝ 0ℝ<ℝ1ℝ} {z = 1ℝ}
    (recipℝ-antitone 1ℝ x 0ℝ<ℝ1ℝ 1≤x) recipℝ-1

------------------------------------------------------------------------
-- Strict antitonicity of the reciprocal
--
-- 倒数的严格反单调性

-- For positive x < y one gets 1/y < 1/x. Multiplying x < y by 1/x gives
-- 1 < y * (1/x); multiplying that by 1/y and cancelling y * (1/y) against
-- one gives 1/y < 1/x. Both transports are purely algebraic, so no case
-- distinction on the strict order is involved.
--
-- 双方为正且 x < y 时得 1/y < 1/x。把 x < y 乘以 1/x 得 1 < y * (1/x)，
-- 再乘以 1/y 并消去 y * (1/y) 即得 1/y < 1/x。两处搬运都是纯代数，
-- 无需对严格序分情况。
recipℝ-strict-antitone-of : (x y : RealI) (0<x : 0ℝ <ℝ x) (0<y : 0ℝ <ℝ y)
                          → x <ℝ y → recipℝ y 0<y <ℝ recipℝ x 0<x
recipℝ-strict-antitone-of x y 0<x 0<y x<y =
  let
    Rx : RealI
    Rx = recipℝ x 0<x

    Ry : RealI
    Ry = recipℝ y 0<y

    0<Rx : 0ℝ <ℝ Rx
    0<Rx = recipℝ-pos x 0<x

    0<Ry : 0ℝ <ℝ Ry
    0<Ry = recipℝ-pos y 0<y

    xRx<yRx : x *ℝ Rx <ℝ y *ℝ Rx
    xRx<yRx = <-*mono x y Rx x<y 0<Rx

    1<yRx : 1ℝ <ℝ y *ℝ Rx
    1<yRx = ≈-<-resp (*ℝ-inverse-pos x 0<x) xRx<yRx

    Ry<yRxRy : 1ℝ *ℝ Ry <ℝ (y *ℝ Rx) *ℝ Ry
    Ry<yRxRy = <-*mono 1ℝ (y *ℝ Rx) Ry 1<yRx 0<Ry

    s1 : (y *ℝ Rx) *ℝ Ry ≈ℝ y *ℝ (Rx *ℝ Ry)
    s1 = *ℝ-assoc y Rx Ry

    s2 : y *ℝ (Rx *ℝ Ry) ≈ℝ y *ℝ (Ry *ℝ Rx)
    s2 = *ℝ-cong (≈ℝ-refl {y}) (*ℝ-comm Rx Ry)

    s3 : y *ℝ (Ry *ℝ Rx) ≈ℝ (y *ℝ Ry) *ℝ Rx
    s3 = ≈ℝ-sym (*ℝ-assoc y Ry Rx)

    s4 : (y *ℝ Ry) *ℝ Rx ≈ℝ 1ℝ *ℝ Rx
    s4 = *ℝ-cong (*ℝ-inverse-pos y 0<y) (≈ℝ-refl {Rx})

    s5 : 1ℝ *ℝ Rx ≈ℝ Rx
    s5 = *ℝ-identityˡ Rx

    yRxRy≈Rx : (y *ℝ Rx) *ℝ Ry ≈ℝ Rx
    yRxRy≈Rx = ≈ℝ-trans s1 (≈ℝ-trans s2 (≈ℝ-trans s3 (≈ℝ-trans s4 s5)))
  in
    ≈-<-respʳ yRxRy≈Rx (≈-<-resp (*ℝ-identityˡ Ry) Ry<yRxRy)

------------------------------------------------------------------------
-- Corollary: the reciprocal of a real above one is below one
--
-- 推论：大于一的实数的倒数小于一

recipℝ-lt-one-of : (x : RealI) (0<x : 0ℝ <ℝ x) (1<x : 1ℝ <ℝ x) →
  recipℝ x 0<x <ℝ 1ℝ
recipℝ-lt-one-of x 0<x 1<x =
  ≈-<-respʳ (*ℝ-inverse-pos x 0<x)
    (≈-<-resp (*ℝ-identityˡ (recipℝ x 0<x))
      (<-*mono 1ℝ x (recipℝ x 0<x) 1<x (recipℝ-pos x 0<x)))

------------------------------------------------------------------------
-- Multiplication and order on intervals
--
-- 区间乘法与序
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Mul.Order where

open import Data.Nat using (ℕ; zero; suc; _^_; s≤s; z≤n; _≥_)
  renaming (_⊔_ to _⊔ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_; _+_ to _+ℕ_; _*_ to _ℕ*_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; *-suc; m<m+n; m≤m+n; ^-monoʳ-≤; *-monoʳ-≤)
  renaming (≤-trans to ≤ℕ-trans; *-comm to *-commℕ; *-identityʳ to *-identityʳℕ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; _⊓_; _⊔_; _+_; _-_; _*_; _<_; _≤_; ∣_∣; nonNegative; positive)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityʳ; neg-distrib-+; neg-distribˡ-*; ≤-trans; <⇒≤; ≤-<-trans
  ; <-≤-trans; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; pos*pos⇒pos; positive⁻¹
  ; *-zeroˡ; ∣-p∣≡∣p∣; ∣p+q∣≤∣p∣+∣q∣; neg-antimono-<; +-mono-<
  ; p≤q⇒p⊓q≡p; ⊓-comm; ⊔-comm; ≮⇒≥; p≤q⊔p; <-irrefl; <-trans; ≤-refl)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive)
open import Real using (embed; ε; half; embed-mono-≤; embed-suc-pos; ε-half)
open import Real.Archimedean using (ε-archimedean)
open import Real.IntervalEquiv using (node; l; u; centre; l-mono; u-mono)
open import Real.Interval using (RealI; δ; δ-pos; pos-pow)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_; negℝ)
open import Real.Interval.ArithLaws using
  (x-ℝx; +ℝ-assoc; +ℝ-inverseˡ; +ℝ-identityˡ; +ℝ-identityʳ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Kit using
  (n≤2n; *-mono-≤-nonNeg; recip-antitone; ≈ℝ-of-eq)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using (*ℝ-distribʳ-+; *ℝ-comm)
open import Real.Interval.Node using
  (node-*ℝ; node-negℝ; centre-add; u-dyadic; l-dyadic; centre-neg; l-neg; u-neg)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLaws using (<-+mono; <-neg; <-sub; ≈-<-resp)
open import Real.Interval.Rational using (sub-add; max-neg; min-neg)

------------------------------------------------------------------------
-- Auxiliary lemmas
--
-- 辅助引理

0<2^n-ℕ : ∀ n → 0 <ℕ 2 ^ n
0<2^n-ℕ zero    = s≤s z≤n
0<2^n-ℕ (suc n) = ≤ℕ-trans (s≤s z≤n) (*-monoʳ-≤ 2 (0<2^n-ℕ n))

2*2^n≡2^n+2^n : ∀ n → 2 ℕ* 2 ^ n ≡ 2 ^ n +ℕ 2 ^ n
2*2^n≡2^n+2^n n =
  begin
    2 ℕ* 2 ^ n
  ≡⟨ *-commℕ 2 (2 ^ n) ⟩
    2 ^ n ℕ* 2
  ≡⟨ *-suc (2 ^ n) 1 ⟩
    2 ^ n +ℕ (2 ^ n ℕ* 1)
  ≡⟨ cong ((2 ^ n) +ℕ_) (*-identityʳℕ (2 ^ n)) ⟩
    2 ^ n +ℕ 2 ^ n
  ∎

sucn≤2^n : ∀ n → suc n ≤ℕ 2 ^ n
sucn≤2^n zero = s≤s z≤n
sucn≤2^n (suc n) =
  let
    ih : suc n ≤ℕ 2 ^ n
    ih = sucn≤2^n n
    step1 : suc (suc n) ≤ℕ suc (2 ^ n)
    step1 = s≤s {m = suc n} {n = 2 ^ n} ih
    step2 : suc (2 ^ n) ≤ℕ 2 ^ n +ℕ 2 ^ n
    step2 = m<m+n (2 ^ n) {2 ^ n} (0<2^n-ℕ n)
    step3 : suc (suc n) ≤ℕ 2 ^ n +ℕ 2 ^ n
    step3 = ≤ℕ-trans step1 step2
    step4 : 2 ^ n +ℕ 2 ^ n ≡ 2 ^ suc n
    step4 = sym (2*2^n≡2^n+2^n n)
  in subst (λ z → suc (suc n) ≤ℕ z) step4 step3

δ≤ε : ∀ j → δ j ≤ ε j
δ≤ε j =
  recip-antitone
    {a = embed (suc j)} {b = embed (2 ^ suc j)}
    (positive⁻¹ (embed (suc j)) {{embed-suc-pos}})
    (embed-mono-≤ suclemma)
  where
    suclemma : suc j ≤ℕ 2 ^ suc j
    suclemma =
      ≤ℕ-trans (sucn≤2^n j)
                (subst (λ z → 2 ^ j ≤ℕ z)
                      (sym (2*2^n≡2^n+2^n j))
                      (m≤m+n (2 ^ j) (2 ^ j)))

δ-mono : ∀ {j K} → j ≤ℕ K → δ K ≤ δ j
δ-mono {j} {K} j≤K =
  recip-antitone
    {a = embed (2 ^ suc j)} {b = embed (2 ^ suc K)}
    (positive⁻¹ (embed (2 ^ suc j)) {{pos-pow j}})
    (embed-mono-≤ (^-monoʳ-≤ 2 (s≤s j≤K)))

neg-max4 : ∀ a b c d →
  neg (((a ⊔ b) ⊔ (c ⊔ d)))
  ≡ ((neg a ⊓ neg b) ⊓ (neg c ⊓ neg d))
neg-max4 a b c d =
  begin
    neg (((a ⊔ b) ⊔ (c ⊔ d)))
  ≡⟨ sym (min-neg (a ⊔ b) (c ⊔ d)) ⟩
    neg (a ⊔ b) ⊓ neg (c ⊔ d)
  ≡⟨ sym (cong₂ _⊓_ (min-neg a b) (min-neg c d)) ⟩
    (neg a ⊓ neg b) ⊓ (neg c ⊓ neg d)
  ∎

neg-min4 : ∀ a b c d →
  neg (((a ⊓ b) ⊓ (c ⊓ d)))
  ≡ ((neg a ⊔ neg b) ⊔ (neg c ⊔ neg d))
neg-min4 a b c d =
  begin
    neg (((a ⊓ b) ⊓ (c ⊓ d)))
  ≡⟨ sym (max-neg (a ⊓ b) (c ⊓ d)) ⟩
    neg (a ⊓ b) ⊔ neg (c ⊓ d)
  ≡⟨ sym (cong₂ _⊔_ (max-neg a b) (max-neg c d)) ⟩
    (neg a ⊔ neg b) ⊔ (neg c ⊔ neg d)
  ∎

l-prod-pos : (a b : RealI) →
  0ℚ < RealI.l a → 0ℚ < RealI.l b →
  RealI.l (a *ℝ b) ≡ RealI.l a * RealI.l b
l-prod-pos a b 0<la 0<lb =
  let
    La = RealI.l a; Ua = RealI.u a
    Lb = RealI.l b; Ub = RealI.u b
    c1 = La * Lb; c2 = La * Ub; c3 = Ua * Lb; c4 = Ua * Ub
    0≤La = <⇒≤ 0<la
    0≤Lb = <⇒≤ 0<lb
    c1≤c2 = *-monoˡ-≤-nonNeg La {{nonNegative 0≤La}} (<⇒≤ (RealI.lo b))
    c1≤c3 = *-monoʳ-≤-nonNeg Lb {{nonNegative 0≤Lb}} (<⇒≤ (RealI.lo a))
    c3≤c4 = *-monoˡ-≤-nonNeg Ua
              {{nonNegative (≤-trans 0≤La (<⇒≤ (RealI.lo a)))}}
              (<⇒≤ (RealI.lo b))
  in   begin
          (c1 ⊓ c2) ⊓ (c3 ⊓ c4)
        ≡⟨ cong (λ z → z ⊓ (c3 ⊓ c4)) (p≤q⇒p⊓q≡p c1≤c2) ⟩
          c1 ⊓ (c3 ⊓ c4)
        ≡⟨ cong (c1 ⊓_) (p≤q⇒p⊓q≡p c3≤c4) ⟩
          c1 ⊓ c3
        ≡⟨ p≤q⇒p⊓q≡p c1≤c3 ⟩
          c1
        ∎

u-dyadic-0 : (K : ℕ) → u 0ℝ K ≡ δ K
u-dyadic-0 K =
  begin
    u 0ℝ K
  ≡⟨ u-dyadic 0ℚ K ⟩
    δ K + 0ℚ
  ≡⟨ +-identityʳ (δ K) ⟩
    δ K
  ∎

abs-neg : ∀ {a b : ℚ} → ∣ neg a - neg b ∣ ≡ ∣ a - b ∣
abs-neg {a} {b} =
  begin
    ∣ neg a - neg b ∣
  ≡⟨ cong ∣_∣ (sym (neg-distrib-+ a (neg b))) ⟩
    ∣ neg (a + neg b) ∣
  ≡⟨ ∣-p∣≡∣p∣ (a - b) ⟩
    ∣ a - b ∣
  ∎

neg-flip : ∀ {x y : ℚ} → neg x < neg y → y < x
neg-flip {x} {y} h =
  subst₂ _<_
    (neg-involutive y) (neg-involutive x)
    (neg-antimono-< {neg x} {neg y} h)

------------------------------------------------------------------------
-- Approximate equality and negation
--
-- 近似相等与否定

≈-neg : {x y : RealI} → x ≈ℝ y → negℝ x ≈ℝ negℝ y
≈-neg {x} {y} p k =
  let N , h = p k
  in N , λ n n≥N →
    let
      d = h n n≥N
      rw : ∣ centre (negℝ x) n - centre (negℝ y) n ∣
         ≡ ∣ centre x n - centre y n ∣
      rw =
        begin
          ∣ centre (negℝ x) n - centre (negℝ y) n ∣
        ≡⟨ cong ∣_∣ (cong₂ _-_ (centre-neg x n) (centre-neg y n)) ⟩
          ∣ neg (centre x n) - neg (centre y n) ∣
        ≡⟨ abs-neg {centre x n} {centre y n} ⟩
          ∣ centre x n - centre y n ∣
        ∎
    in subst (λ w → w < ε k) (sym rw) d

<-neg-inv : {a b : RealI} → negℝ a <ℝ negℝ b → b <ℝ a
<-neg-inv {a} {b} (n , h) = n , goal
  where
    h1 : neg (l a n) < neg (u b n)
    h1 = subst₂ _<_ (u-neg a n) (l-neg b n) h

    goal : u b n < l a n
    goal = neg-flip h1

≈-<-respʳ : {x y z : RealI} → y ≈ℝ z → x <ℝ y → x <ℝ z
≈-<-respʳ {x} {y} {z} y≈z x<y =
  <-neg-inv {a = z} {b = x}
    (≈-<-resp (≈ℝ-sym (≈-neg (≈ℝ-sym y≈z))) (<-neg x y x<y))

≈-<-trans-helper : {a a' b b' : RealI} →
  a ≈ℝ a' → a' <ℝ b' → b' ≈ℝ b → a <ℝ b
≈-<-trans-helper {a} {a'} {b'} {b} a≈a' a'<b' b'≈b =
  ≈-<-respʳ b'≈b (≈-<-resp (≈ℝ-sym a≈a') a'<b')

------------------------------------------------------------------------
-- Negation commutes with multiplication
--
-- 否定与乘法交换

private
  neg-max-min : ∀ La Ua Lb Ub →
    neg (((La * Lb) ⊔ (La * Ub)) ⊔ ((Ua * Lb) ⊔ (Ua * Ub)))
    ≡ (((neg Ua * Lb) ⊓ (neg Ua * Ub)) ⊓ ((neg La * Lb) ⊓ (neg La * Ub)))
  neg-max-min La Ua Lb Ub =
    begin
      neg (((La * Lb) ⊔ (La * Ub)) ⊔ ((Ua * Lb) ⊔ (Ua * Ub)))
    ≡⟨ neg-max4 (La * Lb) (La * Ub) (Ua * Lb) (Ua * Ub) ⟩
      (neg (La * Lb) ⊓ neg (La * Ub)) ⊓ (neg (Ua * Lb) ⊓ neg (Ua * Ub))
    ≡⟨ cong₂ _⊓_
            (cong₂ _⊓_
                    (neg-distribˡ-* La Lb) (neg-distribˡ-* La Ub))
            (cong₂ _⊓_
                    (neg-distribˡ-* Ua Lb) (neg-distribˡ-* Ua Ub)) ⟩
      ((neg La * Lb) ⊓ (neg La * Ub)) ⊓ ((neg Ua * Lb) ⊓ (neg Ua * Ub))
    ≡⟨ ⊓-comm (((neg La) * Lb) ⊓ ((neg La) * Ub))
                (((neg Ua) * Lb) ⊓ ((neg Ua) * Ub)) ⟩
      ((neg Ua * Lb) ⊓ (neg Ua * Ub)) ⊓ ((neg La * Lb) ⊓ (neg La * Ub))
    ∎

  neg-min-max : ∀ La Ua Lb Ub →
    neg (((La * Lb) ⊓ (La * Ub)) ⊓ ((Ua * Lb) ⊓ (Ua * Ub)))
    ≡ (((neg Ua * Lb) ⊔ (neg Ua * Ub)) ⊔ ((neg La * Lb) ⊔ (neg La * Ub)))
  neg-min-max La Ua Lb Ub =
    begin
      neg (((La * Lb) ⊓ (La * Ub)) ⊓ ((Ua * Lb) ⊓ (Ua * Ub)))
    ≡⟨ neg-min4 (La * Lb) (La * Ub) (Ua * Lb) (Ua * Ub) ⟩
      (neg (La * Lb) ⊔ neg (La * Ub)) ⊔ (neg (Ua * Lb) ⊔ neg (Ua * Ub))
    ≡⟨ cong₂ _⊔_
            (cong₂ _⊔_
                    (neg-distribˡ-* La Lb) (neg-distribˡ-* La Ub))
            (cong₂ _⊔_
                    (neg-distribˡ-* Ua Lb) (neg-distribˡ-* Ua Ub)) ⟩
      ((neg La * Lb) ⊔ (neg La * Ub)) ⊔ ((neg Ua * Lb) ⊔ (neg Ua * Ub))
    ≡⟨ ⊔-comm (((neg La) * Lb) ⊔ ((neg La) * Ub))
                (((neg Ua) * Lb) ⊔ ((neg Ua) * Ub)) ⟩
      ((neg Ua * Lb) ⊔ (neg Ua * Ub)) ⊔ ((neg La * Lb) ⊔ (neg La * Ub))
    ∎

negℝ-*ℝ : (x y : RealI) → negℝ (x *ℝ y) ≈ℝ (negℝ x) *ℝ y
negℝ-*ℝ x y = ≈ℝ-of-eq _ _ centre-eq
  where
    l-eq : ∀ n → RealI.l (node (negℝ (x *ℝ y)) n)
                ≡ RealI.l (node ((negℝ x) *ℝ y) n)
    l-eq n =
      let
        a = node x (2 ℕ* n); b = node y (2 ℕ* n)
        La = RealI.l a; Ua = RealI.u a
        Lb = RealI.l b; Ub = RealI.u b

        LHS-unfold :
          RealI.l (node (negℝ (x *ℝ y)) n)
          ≡ neg (((La * Lb) ⊔ (La * Ub)) ⊔ ((Ua * Lb) ⊔ (Ua * Ub)))
        LHS-unfold =
          begin
            RealI.l (node (negℝ (x *ℝ y)) n)
          ≡⟨ cong RealI.l (node-negℝ (x *ℝ y) n) ⟩
            RealI.l (negℝ (node (x *ℝ y) n))
          ≡⟨ cong (λ Z → neg (RealI.u Z)) (node-*ℝ x y n) ⟩
            neg (((La * Lb) ⊔ (La * Ub)) ⊔ ((Ua * Lb) ⊔ (Ua * Ub)))
          ∎

        RHS-unfold :
          RealI.l (node ((negℝ x) *ℝ y) n)
          ≡ ((neg Ua * Lb) ⊓ (neg Ua * Ub)) ⊓ ((neg La * Lb) ⊓ (neg La * Ub))
        RHS-unfold =
          begin
            RealI.l (node ((negℝ x) *ℝ y) n)
          ≡⟨ cong RealI.l (node-*ℝ (negℝ x) y n) ⟩
            RealI.l (node (negℝ x) (2 ℕ* n) *ℝ node y (2 ℕ* n))
          ≡⟨ cong₂ (λ p q → ((p * Lb) ⊓ (p * Ub)) ⊓ ((q * Lb) ⊓ (q * Ub)))
                  (cong RealI.l (node-negℝ x (2 ℕ* n)))
                  (cong RealI.u (node-negℝ x (2 ℕ* n))) ⟩
            ((neg Ua * Lb) ⊓ (neg Ua * Ub)) ⊓ ((neg La * Lb) ⊓ (neg La * Ub))
          ∎
      in  begin
            RealI.l (node (negℝ (x *ℝ y)) n)
          ≡⟨ LHS-unfold ⟩
            neg (((La * Lb) ⊔ (La * Ub)) ⊔ ((Ua * Lb) ⊔ (Ua * Ub)))
          ≡⟨ neg-max-min La Ua Lb Ub ⟩
            ((neg Ua * Lb) ⊓ (neg Ua * Ub)) ⊓ ((neg La * Lb) ⊓ (neg La * Ub))
          ≡˘⟨ RHS-unfold ⟩
            RealI.l (node ((negℝ x) *ℝ y) n)
          ∎

    u-eq : ∀ n → RealI.u (node (negℝ (x *ℝ y)) n)
                ≡ RealI.u (node ((negℝ x) *ℝ y) n)
    u-eq n =
      let
        a = node x (2 ℕ* n); b = node y (2 ℕ* n)
        La = RealI.l a; Ua = RealI.u a
        Lb = RealI.l b; Ub = RealI.u b

        LHS-unfold :
          RealI.u (node (negℝ (x *ℝ y)) n)
          ≡ neg (((La * Lb) ⊓ (La * Ub)) ⊓ ((Ua * Lb) ⊓ (Ua * Ub)))
        LHS-unfold = begin
          RealI.u (node (negℝ (x *ℝ y)) n)
            ≡⟨ cong RealI.u (node-negℝ (x *ℝ y) n) ⟩
          RealI.u (negℝ (node (x *ℝ y) n))
            ≡⟨ cong (λ Z → neg (RealI.l Z)) (node-*ℝ x y n) ⟩
          neg (((La * Lb) ⊓ (La * Ub)) ⊓ ((Ua * Lb) ⊓ (Ua * Ub)))
            ∎

        RHS-unfold :
          RealI.u (node ((negℝ x) *ℝ y) n)
          ≡ ((neg Ua * Lb) ⊔ (neg Ua * Ub)) ⊔ ((neg La * Lb) ⊔ (neg La * Ub))
        RHS-unfold = begin
          RealI.u (node ((negℝ x) *ℝ y) n)
            ≡⟨ cong RealI.u (node-*ℝ (negℝ x) y n) ⟩
          RealI.u (node (negℝ x) (2 ℕ* n) *ℝ node y (2 ℕ* n))
            ≡⟨ cong₂ (λ p q → ((p * Lb) ⊔ (p * Ub)) ⊔ ((q * Lb) ⊔ (q * Ub)))
                     (cong RealI.l (node-negℝ x (2 ℕ* n)))
                     (cong RealI.u (node-negℝ x (2 ℕ* n))) ⟩
          ((neg Ua * Lb) ⊔ (neg Ua * Ub)) ⊔ ((neg La * Lb) ⊔ (neg La * Ub))
            ∎
      in begin
          RealI.u (node (negℝ (x *ℝ y)) n)
            ≡⟨ LHS-unfold ⟩
          neg (((La * Lb) ⊓ (La * Ub)) ⊓ ((Ua * Lb) ⊓ (Ua * Ub)))
            ≡⟨ neg-min-max La Ua Lb Ub ⟩
          ((neg Ua * Lb) ⊔ (neg Ua * Ub)) ⊔ ((neg La * Lb) ⊔ (neg La * Ub))
            ≡⟨ sym RHS-unfold ⟩
          RealI.u (node ((negℝ x) *ℝ y) n)
            ∎

    centre-eq : ∀ n → centre (negℝ (x *ℝ y)) n
                     ≡ centre ((negℝ x) *ℝ y) n
    centre-eq n = cong₂ (λ a b → (a + b) * half) (l-eq n) (u-eq n)

------------------------------------------------------------------------
-- Addition is compatible with approximate equality
--
-- 加法与近似相等相容

+ℝ-cong : {x x' y y' : RealI} → x ≈ℝ x' → y ≈ℝ y' →
          x +ℝ y ≈ℝ x' +ℝ y'
+ℝ-cong {x} {x'} {y} {y'} x≈x' y≈y' k =
  let
    fine = suc (2 ℕ* k)
    N1 , h1 = x≈x' fine
    N2 , h2 = y≈y' fine
    N  = N1 ⊔ℕ N2
  in N , λ n n≥N →
    let
      n≥N1 = ≤ℕ-trans (m≤m⊔n N1 N2) n≥N
      n≥N2 = ≤ℕ-trans (m≤n⊔m N1 N2) n≥N
      d1 = h1 n n≥N1
      d2 = h2 n n≥N2
      cx = centre x n;  cx' = centre x' n
      cy = centre y n;  cy' = centre y' n

      eq : centre (x +ℝ y) n - centre (x' +ℝ y') n
         ≡ (cx - cx') + (cy - cy')
      eq =
        begin
          centre (x +ℝ y) n - centre (x' +ℝ y') n
        ≡⟨ cong₂ _-_ (centre-add x y n) (centre-add x' y' n) ⟩
          (cx + cy) - (cx' + cy')
        ≡⟨ sub-add cx cy cx' cy' ⟩
          (cx - cx') + (cy - cy')
        ∎

      bound : ∣ (cx - cx') + (cy - cy') ∣ ≤ ∣ cx - cx' ∣ + ∣ cy - cy' ∣
      bound = ∣p+q∣≤∣p∣+∣q∣ (cx - cx') (cy - cy')

      cc : ε fine + ε fine ≡ ε k
      cc = ε-half k
    in subst (λ z → ∣ z ∣ < ε k) (sym eq)
         (subst (λ z → ∣ (cx - cx') + (cy - cy') ∣ < z) cc
                (≤-<-trans bound (+-mono-< d1 d2)))

------------------------------------------------------------------------
-- Positivity of product
--
-- 乘积的正性

pos*pos : (a b : RealI) → 0ℝ <ℝ a → 0ℝ <ℝ b → 0ℝ <ℝ a *ℝ b
pos*pos a b (n , δn<lan) (m , δm<lbm) = K , goal
  where
    L = l a n
    M = l b m

    0<L : 0ℚ < L
    0<L = <-≤-trans (δ-pos n)
                    (<⇒≤ (subst (λ z → z < L) (u-dyadic-0 n) δn<lan))

    0<M : 0ℚ < M
    0<M = <-≤-trans (δ-pos m)
                    (<⇒≤ (subst (λ z → z < M) (u-dyadic-0 m) δm<lbm))

    0<LM : 0ℚ < L * M
    0<LM = positive⁻¹ (L * M)
             {{pos*pos⇒pos L {{positive 0<L}} M {{positive 0<M}}}}

    j : ℕ
    j = proj₁ (ε-archimedean (L * M) 0<LM)

    δj<LM : δ j < L * M
    δj<LM = ≤-<-trans (δ≤ε j) (proj₂ (ε-archimedean (L * M) 0<LM))

    K : ℕ
    K = j ⊔ℕ n ⊔ℕ m

    K≥j : K ≥ j
    K≥j = ≤ℕ-trans (m≤m⊔n j n) (m≤m⊔n (j ⊔ℕ n) m)

    K≥n : K ≥ n
    K≥n = ≤ℕ-trans (m≤n⊔m j n) (m≤m⊔n (j ⊔ℕ n) m)

    K≥m : K ≥ m
    K≥m = m≤n⊔m (j ⊔ℕ n) m

    δK<LM : δ K < L * M
    δK<LM = ≤-<-trans (δ-mono K≥j) δj<LM

    2K≥n : 2 ℕ* K ≥ n
    2K≥n = ≤ℕ-trans K≥n (n≤2n K)

    2K≥m : 2 ℕ* K ≥ m
    2K≥m = ≤ℕ-trans K≥m (n≤2n K)

    la' = l a (2 ℕ* K)
    lb' = l b (2 ℕ* K)

    L≤la' : L ≤ la'
    L≤la' = l-mono a 2K≥n

    M≤lb' : M ≤ lb'
    M≤lb' = l-mono b 2K≥m

    0<la' : 0ℚ < la'
    0<la' = <-≤-trans 0<L L≤la'

    0<lb' : 0ℚ < lb'
    0<lb' = <-≤-trans 0<M M≤lb'

    LM≤la'lb' : L * M ≤ la' * lb'
    LM≤la'lb' =
      *-mono-≤-nonNeg (<⇒≤ 0<L) L≤la' (<⇒≤ 0<M) M≤lb'

    l-prod : l (a *ℝ b) K ≡ la' * lb'
    l-prod =
      begin
        l (a *ℝ b) K
      ≡⟨ cong RealI.l (node-*ℝ a b K) ⟩
        RealI.l (node a (2 ℕ* K) *ℝ node b (2 ℕ* K))
      ≡⟨ l-prod-pos (node a (2 ℕ* K)) (node b (2 ℕ* K)) 0<la' 0<lb' ⟩
        la' * lb'
      ∎

    goal : u 0ℝ K < l (a *ℝ b) K
    goal = subst (λ z → z < l (a *ℝ b) K) (sym (u-dyadic-0 K))
             (subst (λ z → δ K < z) (sym l-prod)
                    (<-≤-trans δK<LM LM≤la'lb'))

------------------------------------------------------------------------
-- Subtraction distributes over multiplication
--
-- 减法与乘法分配

mul-sub-distrib : (a b c : RealI) →
  (a -ℝ b) *ℝ c ≈ℝ a *ℝ c -ℝ b *ℝ c
mul-sub-distrib a b c =
  ≈ℝ-trans (*ℝ-distribʳ-+ c a (negℝ b))
  (≈ℝ-trans
    (+ℝ-cong (≈ℝ-refl {a *ℝ c}) (≈ℝ-sym (negℝ-*ℝ b c)))
    (≈ℝ-sym (≈ℝ-refl {a *ℝ c -ℝ b *ℝ c})))

------------------------------------------------------------------------
-- Strict order is preserved by multiplication
--
-- 乘法保持严格序

<-*mono : (x y z : RealI) → x <ℝ y → 0ℝ <ℝ z → x *ℝ z <ℝ y *ℝ z
<-*mono x y z x<y 0<z =
  let
    0<y-x : 0ℝ <ℝ y -ℝ x
    0<y-x = ≈-<-resp (x-ℝx x) (<-sub x y x x<y)

    0<prod : 0ℝ <ℝ (y -ℝ x) *ℝ z
    0<prod = pos*pos (y -ℝ x) z 0<y-x 0<z

    distrib : (y -ℝ x) *ℝ z ≈ℝ y *ℝ z -ℝ x *ℝ z
    distrib = mul-sub-distrib y x z

    0<diff : 0ℝ <ℝ y *ℝ z -ℝ x *ℝ z
    0<diff = ≈-<-respʳ distrib 0<prod

    added : 0ℝ +ℝ (x *ℝ z) <ℝ (y *ℝ z -ℝ x *ℝ z) +ℝ (x *ℝ z)
    added = <-+mono 0ℝ (y *ℝ z -ℝ x *ℝ z) (x *ℝ z) 0<diff

    left-eq : 0ℝ +ℝ (x *ℝ z) ≈ℝ x *ℝ z
    left-eq = +ℝ-identityˡ (x *ℝ z)

    right-eq : (y *ℝ z -ℝ x *ℝ z) +ℝ (x *ℝ z) ≈ℝ y *ℝ z
    right-eq =
      ≈ℝ-trans
        (+ℝ-assoc (y *ℝ z) (negℝ (x *ℝ z)) (x *ℝ z))
        (≈ℝ-trans
          (+ℝ-cong (≈ℝ-refl {y *ℝ z}) (+ℝ-inverseˡ (x *ℝ z)))
          (+ℝ-identityʳ (y *ℝ z)))
  in ≈-<-trans-helper (≈ℝ-sym left-eq) added right-eq

------------------------------------------------------------------------
-- Non-negative multiplication
--
-- 非负乘法

-- The dyadic tolerance is arbitrarily small at a sufficiently deep level.
--
-- 二进容差在足够深的层上可以任意小。
δ-below : (g : ℚ) → 0ℚ < g → (k : ℕ) →
  Σ ℕ (λ m → k ≤ℕ m × δ m < g)
δ-below g 0<g k =
  let
    n , εn<g = ε-archimedean g 0<g
    m = k ⊔ℕ n
    k≤m = m≤m⊔n k n
    n≤m = m≤n⊔m k n
  in m , k≤m , ≤-<-trans (δ-mono n≤m) (≤-<-trans (δ≤ε n) εn<g)

-- The largest corner at level zero bounds the product's upper endpoint.
--
-- 第零层的最大角给出乘积上端点的下界。
u-corner-0 : (a b : RealI) → u a 0 * u b 0 ≤ u (a *ℝ b) 0
u-corner-0 a b =
  let
    chain : u a 0 * u b 0 ≤ u (node a 0 *ℝ node b 0) 0
    chain =
      ≤-trans
        (p≤q⊔p (u a 0 * l b 0) (u a 0 * u b 0))
        (p≤q⊔p ((l a 0 * l b 0) ⊔ (l a 0 * u b 0))
                ((u a 0 * l b 0) ⊔ (u a 0 * u b 0)))
  in subst (λ z → u a 0 * u b 0 ≤ z)
           (sym (cong RealI.u (node-*ℝ a b 0)))
           chain

-- At level n the upper corner at level 2n bounds the product.
--
-- 第 n 层的上端角由第 2n 层的上端点给出下界。
u-prod-corner : (x y : RealI) (n : ℕ) →
  u x (2 ℕ* n) * u y (2 ℕ* n) ≤ u (x *ℝ y) n
u-prod-corner x y n =
  subst (λ z → u x (2 ℕ* n) * u y (2 ℕ* n) ≤ z)
        (sym (cong RealI.u (node-*ℝ x y n)))
        (u-corner-0 (node x (2 ℕ* n)) (node y (2 ℕ* n)))

-- The lower endpoint of the zero interval at level m.
--
-- 零区间在第 m 层的下端点。
l-0 : ∀ m → l 0ℝ m ≡ neg (δ m)
l-0 m =
  begin
    l 0ℝ m
  ≡⟨ l-dyadic 0ℚ m ⟩
    neg (δ m) + 0ℚ
  ≡⟨ +-identityʳ (neg (δ m)) ⟩
    neg (δ m)
  ∎

-- A non-negative real has no negative upper endpoint at any level.
--
-- 非负实数的任何一层上端点都不为负。
u-nonNeg : (x : RealI) → 0ℝ ≤ℝ x → (k : ℕ) → 0ℚ ≤ u x k
u-nonNeg x x≥0 k =
  ≮⇒≥ (λ uk<0 →
    let
      g = neg (u x k)
      0<g : 0ℚ < g
      0<g = neg-antimono-< uk<0
      sel = δ-below g 0<g k
      m = proj₁ sel
      k≤m = proj₁ (proj₂ sel)
      δm<g = proj₂ (proj₂ sel)
      uk≡ : u x k ≡ neg g
      uk≡ = sym (neg-involutive (u x k))
      below : u x k < neg (δ m)
      below = subst (λ z → z < neg (δ m)) (sym uk≡) (neg-antimono-< δm<g)
      um< : u x m < neg (δ m)
      um< = ≤-<-trans (u-mono x k≤m) below
    in x≥0 (m , subst (λ z → u x m < z) (sym (l-0 m)) um<))

-- A product of non-negative reals is non-negative.
--
-- 非负实数之积非负。
*ℝ-nonNeg : (x y : RealI) → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y → 0ℝ ≤ℝ (x *ℝ y)
*ℝ-nonNeg x y x≥0 y≥0 (n , h) =
  let
    c = u x (2 ℕ* n) * u y (2 ℕ* n)
    0≤0y : 0ℚ ≤ 0ℚ * u y (2 ℕ* n)
    0≤0y = subst (λ z → 0ℚ ≤ z) (sym (*-zeroˡ (u y (2 ℕ* n)))) (≤-refl {0ℚ})
    0≤c : 0ℚ ≤ c
    0≤c = ≤-trans 0≤0y
             (*-monoʳ-≤-nonNeg (u y (2 ℕ* n))
               {{nonNegative (u-nonNeg y y≥0 (2 ℕ* n))}}
               (u-nonNeg x x≥0 (2 ℕ* n)))
    0≤u : 0ℚ ≤ u (x *ℝ y) n
    0≤u = ≤-trans 0≤c (u-prod-corner x y n)
    u<neg : u (x *ℝ y) n < neg (δ n)
    u<neg = subst (λ z → u (x *ℝ y) n < z) (l-0 n) h
    negδ<0 : neg (δ n) < 0ℚ
    negδ<0 = neg-antimono-< (δ-pos n)
    u<0 : u (x *ℝ y) n < 0ℚ
    u<0 = <-trans u<neg negδ<0
  in <-irrefl refl (≤-<-trans 0≤u u<0)

-- Non-strict order is preserved by equivalence on the left.
--
-- 非严格序在左侧对等价封闭。
≤-resp-≈ˡ : {x y z : RealI} → x ≈ℝ y → x ≤ℝ z → y ≤ℝ z
≤-resp-≈ˡ {x} {y} {z} x≈y x≤z z<y = x≤z (≈-<-respʳ (≈ℝ-sym x≈y) z<y)

-- Non-strict order is preserved by equivalence on the right.
--
-- 非严格序在右侧对等价封闭。
≤-resp-≈ʳ : {x y z : RealI} → x ≤ℝ y → y ≈ℝ z → x ≤ℝ z
≤-resp-≈ʳ {x} {y} {z} x≤y y≈z z<x = x≤y (≈-<-resp (≈ℝ-sym y≈z) z<x)

-- Multiplication by a non-negative factor preserves non-strict order.
--
-- 非负因子保持非严格序。
*ℝ-≤-mono : (x y z : RealI) → x ≤ℝ y → 0ℝ ≤ℝ z →
  x *ℝ z ≤ℝ y *ℝ z
*ℝ-≤-mono x y z x≤y 0≤z r =
  let
    sum-to-y : (y -ℝ x) +ℝ x ≈ℝ y
    sum-to-y =
      ≈ℝ-trans (+ℝ-assoc y (negℝ x) x)
      (≈ℝ-trans
        (+ℝ-cong (≈ℝ-refl {y}) (+ℝ-inverseˡ x))
        (+ℝ-identityʳ y))
    0≤d : 0ℝ ≤ℝ (y -ℝ x)
    0≤d h =
      x≤y (≈-<-trans-helper (≈ℝ-sym sum-to-y)
             (<-+mono (y -ℝ x) 0ℝ x h)
             (+ℝ-identityˡ x))
    0≤dz : 0ℝ ≤ℝ (y -ℝ x) *ℝ z
    0≤dz = *ℝ-nonNeg (y -ℝ x) z 0≤d 0≤z
    shifted : y *ℝ z -ℝ x *ℝ z <ℝ 0ℝ
    shifted = ≈-<-respʳ (x-ℝx (x *ℝ z))
                (<-sub (y *ℝ z) (x *ℝ z) (x *ℝ z) r)
    corner : (y -ℝ x) *ℝ z <ℝ 0ℝ
    corner = ≈-<-resp (≈ℝ-sym (mul-sub-distrib y x z)) shifted
  in 0≤dz corner

-- Squaring is monotone on non-negative reals.
--
-- 平方在非负实数上单调。
*ℝ-square-mono : (x y : RealI) → 0ℝ ≤ℝ x → x ≤ℝ y →
  x *ℝ x ≤ℝ y *ℝ y
*ℝ-square-mono x y 0≤x x≤y =
  let
    0≤y : 0ℝ ≤ℝ y
    0≤y = ≤ℝ-trans 0≤x x≤y
    left : x *ℝ x ≤ℝ x *ℝ y
    left = ≤-resp-≈ʳ (*ℝ-≤-mono x y x x≤y 0≤x) (≈ℝ-sym (*ℝ-comm x y))
    right : x *ℝ y ≤ℝ y *ℝ y
    right = *ℝ-≤-mono x y y x≤y 0≤y
  in ≤ℝ-trans left right

------------------------------------------------------------------------
-- The logarithm on the whole positive half-line
--
-- 正半轴上的全对数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Log.Full where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _+_; _<_; _≤_; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; <-trans; <-cmp)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Relation.Nullary using (¬_)

open import Real using (embed; 0<embed; 0≤embed; embed-mono-<)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; 1ℝ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (archimedean; dense)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Exp.Approx using (expq-pos)
open import Real.Interval.Exp.Core using (expq)
open import Real.Interval.Exp.Full using
  (expq-total; expq-total-nonNeg; expq-total-mono; expq-total-strict-mono
  ; expq-total-neg-pos)
open import Real.Interval.Exp.Step using (embed≤exp; m<δ+m; neg-δ+m<m)
open import Real.Interval.Inverse using (*ℝ-inverse-pos)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Laws using
  (*ℝ-comm; *ℝ-assoc; *ℝ-identityˡ; *ℝ-identityʳ)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.Order as Ord using (_<ℝ_; <-cotrans; <-irrefl)
  renaming (<-trans to <ℝ-trans)
open import Real.Interval.OrderLe using (<-≤ℝ-trans; ≤ℝ-<trans)
open import Real.Interval.OrderLaws using (≈-<-resp)
open import Real.Interval.OrderComplete.Base using
  (Subset; Upper; Occupied; Located; _≤ℝ_)
open import Real.Interval.OrderComplete using (sup; sup-upper; sup-least)
open import Real.Interval.Reasoning.Equiv
open import Real.Interval.Recip using (recipℝ)
open import Real.Interval.RecipLaws using (recipℝ-pos)
open import Real.Interval.RecipOrder using (recipℝ-strict-antitone-of)
open import Real.Interval.Sqrt.Bounds using (embedℚ-reflect)

------------------------------------------------------------------------
-- Strictness from the failure of the weak order
--
-- 由弱序不成立得严格序

not-le-strict : (a b : ℚ) → Tri (a < b) (a ≡ b) (b < a) → ¬ (b ≤ a) → a < b
not-le-strict a b (tri< a<b _ _) nle = a<b
not-le-strict a b (tri≈ _ eq _) nle =
  ⊥-elim (nle (≤-reflexive (sym eq)))
not-le-strict a b (tri> _ _ b<a) nle = ⊥-elim (nle (<⇒≤ b<a))

------------------------------------------------------------------------
-- The logarithm for 0 < y
--
-- 0 < y 处的对数

module _ (y : RealI) (0<y : 0ℝ <ℝ y) where

  P : Subset
  P x = Σ ℚ (λ q → (x ≈ℝ embedℚ q) × (expq-total q <ℝ y))

  P-member : (q : ℚ) → expq-total q <ℝ y → P (embedℚ q)
  P-member q lt = q , (≈ℝ-refl , lt)

  ----------------------------------------------------------------------
  -- A member below y
  --
  -- 低于 y 的一个成员

  -- Take a natural n with 1/y < embed n and put m = embed (suc n), so
  -- that 0 < m and 1/y < embedℚ m. Then exp m exceeds embedℚ m, hence
  -- 1/exp m < 1/(1/y) ≈ y, and exp (-m) is that reciprocal.
  --
  -- 取自然数 n 使 1/y < embed n，令 m = embed (suc n)，于是 0 < m 且
  -- 1/y < embedℚ m。exp m 高于 embedℚ m，所以 1/exp m < 1/(1/y) ≈ y，
  -- 而 exp (-m) 正是这个倒数。
  R : RealI
  R = recipℝ y 0<y

  0<R : 0ℝ <ℝ R
  0<R = recipℝ-pos y 0<y

  n : ℕ
  n = proj₁ (archimedean R)

  R<en : R <ℝ embedℚ (embed n)
  R<en = proj₂ (archimedean R)

  m : ℚ
  m = embed (suc n)

  0<m : 0ℚ < m
  0<m = 0<embed n

  esn<em : embed n < embed (suc n)
  esn<em = embed-mono-< {m = n} {n = suc n} (n<1+n n)

  R<m : R <ℝ embedℚ m
  R<m = <ℝ-trans R<en (embedℚ-mono (embed n) m esn<em)

  base : embedℚ m ≤ℝ expq m (<⇒≤ 0<m)
  base = embed≤exp m (<⇒≤ 0<m)

  R<expm : R <ℝ expq m (<⇒≤ 0<m)
  R<expm = <-≤ℝ-trans R<m base

  anti : recipℝ (expq m (<⇒≤ 0<m)) (expq-pos m (<⇒≤ 0<m)) <ℝ recipℝ R 0<R
  anti = recipℝ-strict-antitone-of R (expq m (<⇒≤ 0<m)) 0<R (expq-pos m (<⇒≤ 0<m)) R<expm

  invol : recipℝ R 0<R ≈ℝ y
  invol =
    let
      R' : RealI
      R' = recipℝ R 0<R

      R*y≈1 : R *ℝ y ≈ℝ 1ℝ
      R*y≈1 = ≈ℝ-trans (*ℝ-comm R y) (*ℝ-inverse-pos y 0<y)
    in
    beginℝ
      R'
        ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityʳ R') ⟩
      R' *ℝ 1ℝ
        ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym R*y≈1) ⟩
      R' *ℝ (R *ℝ y)
        ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc R' R y) ⟩
      (R' *ℝ R) *ℝ y
        ≈ℝ⟨ *ℝ-cong (≈ℝ-sym (*ℝ-comm R R')) ≈ℝ-refl ⟩
      (R *ℝ R') *ℝ y
        ≈ℝ⟨ *ℝ-cong (*ℝ-inverse-pos R 0<R) ≈ℝ-refl ⟩
      1ℝ *ℝ y
        ≈ℝ⟨ *ℝ-identityˡ y ⟩
      y
    ∎ℝ

  small : recipℝ (expq m (<⇒≤ 0<m)) (expq-pos m (<⇒≤ 0<m)) <ℝ y
  small = ≈-<-respʳ invol anti

  nl : ℚ
  nl = - m

  asm : expq-total nl ≈ℝ
        recipℝ (expq m (<⇒≤ 0<m)) (expq-pos m (<⇒≤ 0<m))
  asm = expq-total-neg-pos m 0<m

  et<y : expq-total nl <ℝ y
  et<y = ≈-<-resp (≈ℝ-sym asm) small

  x₀ : RealI
  x₀ = embedℚ nl

  x₀-member : P x₀
  x₀-member = P-member nl et<y

  ----------------------------------------------------------------------
  -- A rational bound above y
  --
  -- 高于 y 的有理界

  K : ℕ
  K = proj₁ (archimedean y)

  M : ℚ
  M = embed K

  y<eM : y <ℝ embedℚ M
  y<eM = proj₂ (archimedean y)

  isUpper : (x : RealI) → P x → x ≤ℝ embedℚ M
  isUpper x (r , (x≈ , er<y)) h =
    let
      eM<er : embedℚ M <ℝ embedℚ r
      eM<er = ≈-<-respʳ x≈ h

      M<r : M < r
      M<r = embedℚ-reflect M r eM<er

      0≤r : 0ℚ ≤ r
      0≤r = ≤-trans (0≤embed K) (<⇒≤ M<r)

      em<exp : embedℚ M <ℝ expq r 0≤r
      em<exp = <-≤ℝ-trans (embedℚ-mono M r M<r) (embed≤exp r 0≤r)

      exp<em : expq r 0≤r <ℝ embedℚ M
      exp<em = <ℝ-trans
                 (≈-<-resp (expq-total-nonNeg r 0≤r) er<y)
                 y<eM
    in
      <-irrefl (embedℚ M) (<ℝ-trans em<exp exp<em)

  ----------------------------------------------------------------------
  -- Everything above y is beyond the upper bound
  --
  -- 凡指数高于 y 的点都在上界之外

  upper-above : (q : ℚ) → y <ℝ expq-total q → Upper P q
  upper-above q y<eq x (r , (x≈ , er<y)) =
    let
      lt : expq-total r <ℝ expq-total q
      lt = <ℝ-trans er<y y<eq

      nle : ¬ (q ≤ r)
      nle q≤r = <-irrefl (expq-total q)
                  (≤ℝ-<trans (expq-total-mono q r q≤r) lt)

      r<q : r < q
      r<q = not-le-strict r q (<-cmp r q) nle
    in
      ≈-<-resp (≈ℝ-sym x≈) (embedℚ-mono r q r<q)

  ----------------------------------------------------------------------
  -- Locatedness
  --
  -- 定位性

  locate : (p q s : ℚ) → embedℚ p <ℝ embedℚ s
         → expq-total s <ℝ y ⊎ y <ℝ expq-total q
         → Occupied P p ⊎ Upper P q
  locate p q s ep<es (inj₁ es<y) =
    inj₁ (embedℚ s , (P-member s es<y , ep<es))
  locate p q s ep<es (inj₂ y<eq) = inj₂ (upper-above q y<eq)

  locate-mid : (p q : ℚ)
             → Σ ℚ (λ s → (embedℚ p <ℝ embedℚ s) × (embedℚ s <ℝ embedℚ q))
             → Occupied P p ⊎ Upper P q
  locate-mid p q (s , (ep<es , es<eq)) =
    locate p q s ep<es
      (<-cotrans {x = expq-total s} {y = y} {z = expq-total q}
                 (expq-total-strict-mono s q (embedℚ-reflect s q es<eq)))

  located : Located P
  located p q p<q =
    locate-mid p q (dense {x = embedℚ p} {y = embedℚ q} (embedℚ-mono p q p<q))

  ----------------------------------------------------------------------
  -- The logarithm
  --
  -- 对数

  logℝ-total : RealI
  logℝ-total = sup {P = P} located {x₀ = x₀} x₀-member {u₀ = embedℚ M} isUpper

  log-total-upper : (x : RealI) → P x → x ≤ℝ logℝ-total
  log-total-upper = sup-upper {P = P} located {x₀ = x₀} x₀-member
                             {u₀ = embedℚ M} isUpper

  log-total-least : (u₀ : RealI) → ((x : RealI) → P x → x ≤ℝ u₀)
                  → logℝ-total ≤ℝ u₀
  log-total-least = sup-least {P = P} located {x₀ = x₀} x₀-member
                              {u₀ = embedℚ M} isUpper

  log-total-member : (q : ℚ) → expq-total q <ℝ y → embedℚ q ≤ℝ logℝ-total
  log-total-member q lt = log-total-upper (embedℚ q) (P-member q lt)

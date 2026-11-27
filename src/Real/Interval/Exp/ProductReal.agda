------------------------------------------------------------------------
-- The product of real partial sums against the doubled partial sum
--
-- 实部分和之积与倍长部分和
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.ProductReal where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; positive; _≤_; _<_; _+_; _*_)
open import Data.Rational.Properties using
  (≤-trans; ≤-<-trans; +-monoʳ-<; *-comm; *-identityˡ; *-zeroˡ; *-monoˡ-<-pos)

open import Real using (half)
open import Real.Archimedean using (le-add-right)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (_+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using (sub-add-cancelℝ)
open import Real.Interval.Continuity using (Close; embedℚ-mono)
open import Real.Interval.Embed using (embedℚ-+; embedℚ-*)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Elementary.ExpRat using (expPartialℝ-at-rat)
open import Real.Interval.Exp.Core using (expPartial)
open import Real.Interval.Exp.Series using (expPartialℝ)
open import Real.Interval.Exp.ProductClose using (expPartial-add-close)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using (+ℝ-cong; ≈-<-respʳ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using (<-+mono-reflect)
open import Real.Interval.OrderLaws using
  (≈-<-resp; halved-tolerance-pos; halved-tolerance-below)

------------------------------------------------------------------------
-- A strict rational gap survives the embedding
--
-- 有理间隙经嵌入仍严格

embedℚ-add-lt : (a b d : ℚ) → a < b + d → embedℚ a <ℝ embedℚ b +ℝ embedℚ d
embedℚ-add-lt a b d a<b+d =
  ≈-<-respʳ (embedℚ-+ b d) (embedℚ-mono a (b + d) a<b+d)

------------------------------------------------------------------------
-- The real product equals the embedded rational product
--
-- 实部分和之积等于有理乘积的嵌入

expPartialℝ-mul-rat : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (n : ℕ)
                    → expPartialℝ (embedℚ p) n *ℝ expPartialℝ (embedℚ q) n
                      ≈ℝ embedℚ (expPartial p n * expPartial q n)
expPartialℝ-mul-rat p q 0≤p 0≤q n =
  ≈ℝ-trans
    (*ℝ-cong (expPartialℝ-at-rat p 0≤p n) (expPartialℝ-at-rat q 0≤q n))
    (≈ℝ-sym (embedℚ-* (expPartial p n) (expPartial q n)))

------------------------------------------------------------------------
-- The product meets the doubled sum at a late index
--
-- 乘积在足够后的指标处贴近倍长和

expPartial-add-close-rat :
  (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
  → Σ ℕ (λ N → ∀ n → N ≤ℕ n
      → Close d (expPartialℝ (embedℚ p) n *ℝ expPartialℝ (embedℚ q) n)
                (expPartialℝ (embedℚ (p + q)) (n +ℕ n)))
expPartial-add-close-rat p q 0≤p 0≤q d 0<d =
  let
    d₂ : ℚ
    d₂ = d * half

    0<d₂ : 0ℚ < d₂
    0<d₂ = halved-tolerance-pos d 0<d

    d₂<d : d₂ < d
    d₂<d = halved-tolerance-below d 0<d

    close : Σ ℕ (λ N → ∀ n → N ≤ℕ n
              → (expPartial p n * expPartial q n
                   ≤ expPartial (p + q) (n +ℕ n) + d₂)
                × (expPartial (p + q) (n +ℕ n)
                   ≤ expPartial p n * expPartial q n + d₂))
    close = expPartial-add-close p q 0≤p 0≤q d₂ 0<d₂

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)
  in
    proj₁ close , λ n N≤n →
      let
        a : ℚ
        a = expPartial p n * expPartial q n

        b : ℚ
        b = expPartial (p + q) (n +ℕ n)

        a<b+d : a < b + d
        a<b+d = ≤-<-trans (proj₁ (proj₂ close n N≤n)) (+-monoʳ-< b d₂<d)

        b<a+d : b < a + d
        b<a+d = ≤-<-trans (proj₂ (proj₂ close n N≤n)) (+-monoʳ-< a d₂<d)

        A : RealI
        A = expPartialℝ (embedℚ p) n *ℝ expPartialℝ (embedℚ q) n

        B : RealI
        B = expPartialℝ (embedℚ (p + q)) (n +ℕ n)

        A≈ : A ≈ℝ embedℚ a
        A≈ = expPartialℝ-mul-rat p q 0≤p 0≤q n

        B≈ : B ≈ℝ embedℚ b
        B≈ = expPartialℝ-at-rat (p + q) 0≤pq (n +ℕ n)

        left₀ : A <ℝ embedℚ b +ℝ embedℚ d
        left₀ = ≈-<-resp (≈ℝ-sym A≈) (embedℚ-add-lt a b d a<b+d)

        left₁ : A <ℝ B +ℝ embedℚ d
        left₁ = ≈-<-respʳ (+ℝ-cong (≈ℝ-sym B≈) (≈ℝ-refl {embedℚ d})) left₀

        left₂ : (A -ℝ embedℚ d) +ℝ embedℚ d <ℝ B +ℝ embedℚ d
        left₂ = ≈-<-resp (≈ℝ-sym (sub-add-cancelℝ A (embedℚ d))) left₁

        right₀ : B <ℝ embedℚ a +ℝ embedℚ d
        right₀ = ≈-<-resp (≈ℝ-sym B≈) (embedℚ-add-lt b a d b<a+d)

        right₁ : B <ℝ A +ℝ embedℚ d
        right₁ = ≈-<-respʳ (+ℝ-cong (≈ℝ-sym A≈) (≈ℝ-refl {embedℚ d})) right₀
      in
        <-+mono-reflect {x = B} {y = A -ℝ embedℚ d} {z = embedℚ d} left₂
          , right₁

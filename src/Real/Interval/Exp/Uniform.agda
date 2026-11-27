------------------------------------------------------------------------
-- Tail bounds transfer along the parameter
--
-- 尾界沿参数传递
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Uniform where

open import Data.Nat using (ℕ; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties as NatP using (≤-total; m+[n∸m]≡n)
open import Data.Rational using (ℚ; 0ℚ; _≤_; _<_; _+_; _-_; _*_)
open import Data.Rational.Base using (-_; nonNegative)
open import Data.Rational.Properties using
  ( ≤-trans; <⇒≤; +-assoc; +-comm; +-identityʳ; +-inverseʳ; +-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; cong; trans; subst)

open import Real.Interval.Rational using (add-then-drop)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Exp.Core using
  (expPartial; expPartial-le; sumQ; sumQ-split; sumQ-mono; sub-le-shift
  ; term; _≤ℕ_)
open import Real.Interval.Exp.Order using (term-mono)
open import Real.Interval.Exp.Bracket using (sum-const)

------------------------------------------------------------------------
-- The tail at a smaller parameter
--
-- 较小参数处的尾段

tail-transfer : (q Q : ℚ) (0≤q : 0ℚ ≤ q) (q≤Q : q ≤ Q)
                (N : ℕ) (d : ℚ) (0<d : 0ℚ < d)
                (cert : (m : ℕ) → N ≤ℕ m → expPartial Q m ≤ expPartial Q N + d)
                (m : ℕ) → N ≤ℕ m → expPartial q m ≤ expPartial q N + d
tail-transfer q Q 0≤q q≤Q N d 0<d cert m N≤m =
  let
    eqm : N +ℕ (m ∸ N) ≡ m
    eqm = m+[n∸m]≡n {N} {m} N≤m

    S : ℚ
    S = sumQ (λ i → term q (N +ℕ i)) (m ∸ N)

    T : ℚ
    T = sumQ (λ i → term Q (N +ℕ i)) (m ∸ N)

    sq : expPartial q m ≡ expPartial q N + S
    sq = trans (cong (expPartial q) (sym eqm)) (sumQ-split (term q) N (m ∸ N))

    sqQ : expPartial Q m ≡ expPartial Q N + T
    sqQ = trans (cong (expPartial Q) (sym eqm)) (sumQ-split (term Q) N (m ∸ N))

    S≤T : S ≤ T
    S≤T = sumQ-mono (λ i → term q (N +ℕ i)) (λ i → term Q (N +ℕ i))
                    (λ i → term-mono q Q 0≤q q≤Q (N +ℕ i)) (m ∸ N)

    cert' : expPartial Q m ≤ d + expPartial Q N
    cert' = subst (λ z → expPartial Q m ≤ z)
                  (+-comm (expPartial Q N) d) (cert m N≤m)

    T≤d₀ : expPartial Q m - expPartial Q N ≤ d
    T≤d₀ = sub-le-shift (expPartial Q m) (expPartial Q N) d cert'

    drop : expPartial Q m - expPartial Q N ≡ T
    drop = trans (cong (λ z → z - expPartial Q N) sqQ)
                 (add-then-drop (expPartial Q N) T)

    T≤d : T ≤ d
    T≤d = subst (λ z → z ≤ d) drop T≤d₀

    S≤d : S ≤ d
    S≤d = ≤-trans S≤T T≤d

    chain : expPartial q N + S ≤ expPartial q N + d
    chain = +-monoʳ-≤ (expPartial q N) S≤d
  in
    subst (λ z → z ≤ expPartial q N + d) (sym sq) chain

------------------------------------------------------------------------
-- A global bound at the smaller parameter
--
-- 较小参数处的整体界

expPartial-bound-of-tail : (q Q : ℚ) (0≤q : 0ℚ ≤ q) (q≤Q : q ≤ Q)
                           (N : ℕ) (d : ℚ) (0<d : 0ℚ < d)
                           (cert : (m : ℕ) → N ≤ℕ m → expPartial Q m ≤ expPartial Q N + d)
                         → (j : ℕ) → expPartial q j ≤ expPartial q N + d
expPartial-bound-of-tail q Q 0≤q q≤Q N d 0<d cert j =
  sum-const (λ j≤N → ≤-trans (expPartial-le q 0≤q j N j≤N)
                 (le-self-add {p = expPartial q N} {q = d} (<⇒≤ 0<d)))
            (λ N≤j → tail-transfer q Q 0≤q q≤Q N d 0<d cert j N≤j)
            (NatP.≤-total j N)

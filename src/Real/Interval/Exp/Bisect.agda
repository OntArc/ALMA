------------------------------------------------------------------------
-- Halving a bracket on a decidable rational predicate
--
-- 在可判定有理谓词上折半收缩括号
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Bisect where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_)
open import Data.Rational.Base using (_-_; -_; nonNegative)
open import Data.Rational.Properties using
  ( ≤-refl; <⇒≤  )
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; trans; subst)
open import Data.Rational.Properties using
  ( ≤-trans; +-assoc; +-comm; +-inverseʳ; +-identityˡ; +-identityʳ
  ; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-zeroʳ; *-distribʳ-+
  ; +-monoˡ-≤; +-monoʳ-≤; *-monoˡ-≤-nonNeg)

open import Real using (half)
open import Real.IntervalEquiv using (recipPow2)
open import Real.Interval.Rational using (plus-diff)
open import Real.Interval.Kit using
  (0≤half; half≤1; half+half≡1; *-mono-≤-nonNeg; 0≤diff)
open import Real.Interval.Series.Bounds using
  (le-self-add; recipPow2-0; recipPow2-suc)

------------------------------------------------------------------------
-- Case elimination at a constant result type
--
-- 常结果类型的和消去

sum-branch : {A P : Set} → P ⊎ (P → ⊥) → (P → A) → ((P → ⊥) → A) → A
sum-branch (inj₁ p) f g = f p
sum-branch (inj₂ np) f g = g np

------------------------------------------------------------------------
-- The bracket state
--
-- 括号状态

Bracket : (P : ℚ → Set) (a b : ℚ) (k : ℕ) → Set
Bracket P a b k =
  Σ ℚ (λ x → Σ ℚ (λ h →
    P x × ((P (x + h)) → ⊥) × ((x + h) ≤ b) × (0ℚ ≤ h) × (a ≤ x)
    × (h ≡ (b - a) * recipPow2 k)))

------------------------------------------------------------------------
-- A left end within the bracket is below the right end
--
-- 括号内的左端在右端之下

left-below-right : (P : ℚ → Set) (a b : ℚ) (k : ℕ)
                 → Bracket P a b k → Σ ℚ (λ x → Σ ℚ (λ h →
                     P x × ((P (x + h)) → ⊥) × (0ℚ ≤ h) × (a ≤ x) × (x ≤ b)))
left-below-right P a b k (x , h , br) =
  let Px = proj₁ br
      nPh = proj₁ (proj₂ br)
      xh≤b = proj₁ (proj₂ (proj₂ br))
      0≤h = proj₁ (proj₂ (proj₂ (proj₂ br)))
      a≤x = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ br))))
  in x , h , Px , nPh , 0≤h , a≤x
       , ≤-trans (le-self-add {p = x} {q = h} 0≤h) xh≤b

------------------------------------------------------------------------
-- Two rational identities used by the halving step
--
-- 折半步骤用到的两个有理等式

-- h * half + h * half ≡ h, i.e. the two halves reassemble the width.
--
-- h * half + h * half ≡ h，即两个半宽重新合成整宽。
half-add : (h : ℚ) → h * half + h * half ≡ h
half-add h =
  trans (cong₂ _+_ (*-comm h half) (*-comm h half))
    (trans (sym (*-distribʳ-+ h half half))
      (trans (cong (_* h) half+half≡1) (*-identityˡ h)))

-- (x + h * half) + h * half ≡ x + h, the halving step of the left end.
--
-- (x + h * half) + h * half ≡ x + h，折半后左端的递推。
halve-left : (x h : ℚ) → (x + h * half) + h * half ≡ x + h
halve-left x h = trans (+-assoc x (h * half) (h * half))
                  (cong (x +_) (half-add h))

-- h * half ≤ h for non-negative h: multiplying by half does not grow.
--
-- 非负 h 满足 h * half ≤ h：乘半不增大。
hh-le : (h : ℚ) → 0ℚ ≤ h → h * half ≤ h
hh-le h 0≤h =
  subst (λ z → h * half ≤ z) (*-identityʳ h)
    (*-monoˡ-≤-nonNeg h {{nonNegative 0≤h}} half≤1)

-- A half of a non-negative is non-negative.
--
-- 非负数的一半仍非负。
0≤hh : (h : ℚ) → 0ℚ ≤ h → 0ℚ ≤ h * half
0≤hh h 0≤h =
  subst (λ z → z ≤ h * half) (*-zeroʳ 0ℚ)
    (*-mono-≤-nonNeg {a = 0ℚ} {a' = h} {b = 0ℚ} {b' = half}
      (≤-refl {0ℚ}) 0≤h (≤-refl {0ℚ}) 0≤half)

------------------------------------------------------------------------
-- The bisection
--
-- 二分

bisect : (P : ℚ → Set) (split : (x : ℚ) → P x ⊎ ((P x) → ⊥))
         (a b : ℚ) (a<b : a < b) (Pa : P a) (nb : P b → ⊥)
       → (k : ℕ) → Bracket P a b k
bisect P split a b a<b Pa nb zero =
  let
    h : ℚ
    h = b - a

    ab : a + (b - a) ≡ b
    ab = plus-diff a b

    nPh : P (a + h) → ⊥
    nPh = subst (λ z → P z → ⊥) (sym ab) nb

    le : (a + h) ≤ b
    le = subst (λ z → z ≤ b) (sym ab) (≤-refl {b})

    ge : 0ℚ ≤ h
    ge = 0≤diff {a = a} {b = b} (<⇒≤ a<b)

    heq : h ≡ (b - a) * recipPow2 zero
    heq = trans (sym (*-identityʳ (b - a)))
                 (cong ((b - a) *_) (sym recipPow2-0))
  in
    a , h , Pa , nPh , le , ge , ≤-refl {a} , heq
bisect P split a b a<b Pa nb (suc k) =
  let
    (x , h , Px , nPh , xh≤b , 0≤h , a≤x , heq) = bisect P split a b a<b Pa nb k

    hh : ℚ
    hh = h * half

    mh-eq : (x + h * half) + h * half ≡ x + h
    mh-eq = halve-left x h

    le-hh : hh ≤ h
    le-hh = hh-le h 0≤h

    ge-hh : 0ℚ ≤ hh
    ge-hh = 0≤hh h 0≤h

    heq-hh : hh ≡ (b - a) * recipPow2 (suc k)
    heq-hh = trans (cong (_* half) heq)
               (trans (*-assoc (b - a) (recipPow2 k) half)
                 (cong ((b - a) *_) (sym (recipPow2-suc k))))
  in
    sum-branch (split (x + h * half))
      (λ Pm →
        let
          le : (x + h * half) + hh ≤ b
          le = subst (λ z → z ≤ b) (sym mh-eq) xh≤b

          np : P ((x + h * half) + hh) → ⊥
          np = subst (λ z → P z → ⊥) (sym mh-eq) nPh

          ax : a ≤ x + h * half
          ax = ≤-trans a≤x (le-self-add {p = x} {q = hh} ge-hh)
        in
          (x + h * half) , hh , Pm , np , le , ge-hh , ax , heq-hh)
      (λ nPm →
        let
          le : x + hh ≤ b
          le = ≤-trans (+-monoʳ-≤ x le-hh) xh≤b
        in
          x , hh , Px , nPm , le , ge-hh , a≤x , heq-hh)

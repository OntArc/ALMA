------------------------------------------------------------------------
-- The product of partial sums against the doubled sum
--
-- 部分和之积与倍长和之差
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.ProductClose where

open import Data.Nat using (ℕ; _∸_) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; _*_; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; +-mono-≤; <⇒≤; *-comm; +-assoc; +-comm; +-identityˡ
  ; +-inverseʳ; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Base.RationalRing using (0<1)
open import Real using (ε; 0<ε)
open import Real.Archimedean using (rat-shrink)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Kit using (*-mono-≤-nonNeg)
open import Real.Interval.Exp.Core using
  (term; sumQ; sumQ-split; sumQ-nonNeg; term-nonNeg; expPartial
  ; expPartial-mono; exp-bracket)
open import Real.Interval.Exp.ProductBound using (partial-mul-≤; ≤-of-≡)
open import Real.Interval.Exp.ProductTail using (tail; partial-mul-upper)

------------------------------------------------------------------------
-- Cancellation on the left of the order
--
-- 序关系左端的消去

-- Adding the same summand on the left of both sides of an inequality can
-- be undone.
--
-- 不等式两端左端加上同一被加项，可以再消去。
add-cancel-≤ : (a t u : ℚ) → a + t ≤ a + u → t ≤ u
add-cancel-≤ a t u h =
  let e1 : (a + t) + (- a) ≡ t
      e1 = trans (+-assoc a t (- a))
             (trans (cong (a +_) (+-comm t (- a)))
               (trans (sym (+-assoc a (- a) t))
                 (trans (cong (_+ t) (+-inverseʳ a)) (+-identityˡ t))))
      e2 : (a + u) + (- a) ≡ u
      e2 = trans (+-assoc a u (- a))
             (trans (cong (a +_) (+-comm u (- a)))
               (trans (sym (+-assoc a (- a) u))
                 (trans (cong (_+ u) (+-inverseʳ a)) (+-identityˡ u))))
      step : (a + t) + (- a) ≤ (a + u) + (- a)
      step = +-mono-≤ h (≤-refl { - a })
  in subst₂ (λ z w → z ≤ w) e1 e2 step

------------------------------------------------------------------------
-- Reading the bracket at any later index
--
-- 在任意更后的指标处读括号

-- Past the bracket index the partial sums stay below the bracket.
--
-- 越过括号指标之后，部分和留在括号之内。
partial-of-bracket : (q : ℚ) (0≤q : 0ℚ ≤ q) (N : ℕ) (d : ℚ)
                   → (∀ j → expPartial q (N +ℕ j) ≤ expPartial q N + d)
                   → (n : ℕ) → N ≤ℕ n
                   → expPartial q n ≤ expPartial q N + d
partial-of-bracket q 0≤q N d br n N≤n =
  subst (λ z → expPartial q z ≤ expPartial q N + d)
        (NatP.m+[n∸m]≡n N≤n) (br (n ∸ N))

-- Past the bracket index the tail of length `n` stays below the bracket
-- tolerance.
--
-- 越过括号指标之后，长度为 `n` 的尾段留在括号的容差之下。
tail-of-bracket : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d) (N : ℕ)
                → (∀ j → expPartial q (N +ℕ j) ≤ expPartial q N + d)
                → (n : ℕ) → N ≤ℕ n
                → tail q n ≤ d
tail-of-bracket q 0≤q d 0<d N br n N≤n =
  let nn : N ≤ℕ n +ℕ n
      nn = NatP.≤-trans N≤n (NatP.m≤m+n n n)
      split : expPartial q n + tail q n ≡ expPartial q (n +ℕ n)
      split = sym (sumQ-split (term q) n n)
      up : expPartial q (n +ℕ n) ≤ expPartial q N + d
      up = subst (λ z → expPartial q z ≤ expPartial q N + d)
                 (NatP.m+[n∸m]≡n nn) (br ((n +ℕ n) ∸ N))
      mono : expPartial q N ≤ expPartial q n
      mono = subst (λ z → expPartial q N ≤ expPartial q z)
                   (NatP.m+[n∸m]≡n N≤n) (expPartial-mono q 0≤q N (n ∸ N))
      ladder : expPartial q n + tail q n ≤ expPartial q n + d
      ladder = ≤-trans (≤-of-≡ _ _ split)
                 (≤-trans up (+-mono-≤ mono (≤-refl {d})))
  in add-cancel-≤ (expPartial q n) (tail q n) d ladder

------------------------------------------------------------------------
-- Non-negativity of the ingredients
--
-- 各成分的非负性

partial-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (n : ℕ)
                → 0ℚ ≤ expPartial q n
partial-nonNeg q 0≤q n =
  sumQ-nonNeg (term q) (λ i → term-nonNeg q 0≤q i) n

tail-nonNeg : (q : ℚ) (0≤q : 0ℚ ≤ q) (n : ℕ)
            → 0ℚ ≤ tail q n
tail-nonNeg q 0≤q n =
  sumQ-nonNeg (λ i → term q (n +ℕ i))
              (λ i → term-nonNeg q 0≤q (n +ℕ i)) n

plus1-nonNeg : (x : ℚ) → 0ℚ ≤ x → 0ℚ ≤ x + 1ℚ
plus1-nonNeg x 0≤x = ≤-trans 0≤x (le-self-add {p = x} (<⇒≤ 0<1))

add-nonNeg : (a b : ℚ) → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
add-nonNeg a b 0≤a 0≤b = ≤-trans 0≤a (le-self-add {p = a} 0≤b)

-- The two tail corrections fit under `d`.
--
-- 两条尾部修正落在 `d` 之下。
corr-≤′ :
  (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (d : ℚ)
  (Np₀ Nq₀ Np Nq : ℕ) (j : ℕ)
  (brp₀ : ∀ k → expPartial p (Np₀ +ℕ k) ≤ expPartial p Np₀ + 1ℚ)
  (brq₀ : ∀ k → expPartial q (Nq₀ +ℕ k) ≤ expPartial q Nq₀ + 1ℚ)
  (brp  : ∀ k → expPartial p (Np +ℕ k) ≤ expPartial p Np + ε j)
  (brq  : ∀ k → expPartial q (Nq +ℕ k) ≤ expPartial q Nq + ε j)
  (shrink : (ε j) * ((expPartial p Np₀ + 1ℚ)
                   + (expPartial q Nq₀ + 1ℚ)) < d)
  (n : ℕ) → Np₀ ≤ℕ n → Nq₀ ≤ℕ n → Np ≤ℕ n → Nq ≤ℕ n
  → expPartial p n * tail q n + tail p n * expPartial q n ≤ d
corr-≤′ p q 0≤p 0≤q d Np₀ Nq₀ Np Nq j
        brp₀ brq₀ brp brq shrink n Np₀≤n Nq₀≤n Np≤n Nq≤n =
  let
    Gp : ℚ
    Gp = expPartial p Np₀ + 1ℚ
    Gq : ℚ
    Gq = expPartial q Nq₀ + 1ℚ
    Pp≤ : expPartial p n ≤ Gp
    Pp≤ = partial-of-bracket p 0≤p Np₀ 1ℚ brp₀ n Np₀≤n
    Pq≤ : expPartial q n ≤ Gq
    Pq≤ = partial-of-bracket q 0≤q Nq₀ 1ℚ brq₀ n Nq₀≤n
    tailq≤ : tail q n ≤ (ε j)
    tailq≤ = tail-of-bracket q 0≤q (ε j) (0<ε j) Nq brq n Nq≤n
    tailp≤ : tail p n ≤ (ε j)
    tailp≤ = tail-of-bracket p 0≤p (ε j) (0<ε j) Np brp n Np≤n
    0≤Pp : 0ℚ ≤ expPartial p n
    0≤Pp = partial-nonNeg p 0≤p n
    0≤Pq : 0ℚ ≤ expPartial q n
    0≤Pq = partial-nonNeg q 0≤q n
    0≤tp : 0ℚ ≤ tail p n
    0≤tp = tail-nonNeg p 0≤p n
    0≤tq : 0ℚ ≤ tail q n
    0≤tq = tail-nonNeg q 0≤q n
    c1 : expPartial p n * tail q n ≤ Gp * (ε j)
    c1 = *-mono-≤-nonNeg 0≤Pp Pp≤ 0≤tq tailq≤
    c2 : tail p n * expPartial q n ≤ (ε j) * Gq
    c2 = *-mono-≤-nonNeg 0≤tp tailp≤ 0≤Pq Pq≤
    dist : Gp * (ε j) + (ε j) * Gq
         ≡ (ε j) * ((expPartial p Np₀ + 1ℚ)
                  + (expPartial q Nq₀ + 1ℚ))
    dist = trans (cong₂ _+_ (*-comm Gp (ε j)) refl)
                 (sym (*-distribˡ-+ (ε j) Gp Gq))
  in ≤-trans (+-mono-≤ c1 c2)
       (≤-trans (≤-of-≡ _ _ dist) (<⇒≤ shrink))

-- The two-sided half of the estimate.
--
-- 双边估计的一半。
half′ :
  (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
  (Np₀ Nq₀ Np Nq : ℕ) (j : ℕ)
  (brp₀ : ∀ k → expPartial p (Np₀ +ℕ k) ≤ expPartial p Np₀ + 1ℚ)
  (brq₀ : ∀ k → expPartial q (Nq₀ +ℕ k) ≤ expPartial q Nq₀ + 1ℚ)
  (brp  : ∀ k → expPartial p (Np +ℕ k) ≤ expPartial p Np + ε j)
  (brq  : ∀ k → expPartial q (Nq +ℕ k) ≤ expPartial q Nq + ε j)
  (shrink : (ε j) * ((expPartial p Np₀ + 1ℚ)
                   + (expPartial q Nq₀ + 1ℚ)) < d)
  (n : ℕ) → (((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq) ≤ℕ n
  → (expPartial p n * expPartial q n
       ≤ expPartial (p + q) (n +ℕ n) + d)
    × (expPartial (p + q) (n +ℕ n)
       ≤ expPartial p n * expPartial q n + d)
half′ p q 0≤p 0≤q d 0<d Np₀ Nq₀ Np Nq j
      brp₀ brq₀ brp brq shrink n N≤n =
  let
    Np₀≤N : Np₀ ≤ℕ ((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq
    Np₀≤N = NatP.≤-trans (NatP.≤-trans (NatP.m≤m+n Np₀ Nq₀)
                              (NatP.m≤m+n (Np₀ +ℕ Nq₀) Np))
                       (NatP.m≤m+n ((Np₀ +ℕ Nq₀) +ℕ Np) Nq)
    Nq₀≤N : Nq₀ ≤ℕ ((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq
    Nq₀≤N = NatP.≤-trans (NatP.≤-trans (NatP.m≤n+m Nq₀ Np₀)
                              (NatP.m≤m+n (Np₀ +ℕ Nq₀) Np))
                       (NatP.m≤m+n ((Np₀ +ℕ Nq₀) +ℕ Np) Nq)
    Np≤N : Np ≤ℕ ((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq
    Np≤N = NatP.≤-trans (NatP.m≤n+m Np (Np₀ +ℕ Nq₀))
                       (NatP.m≤m+n ((Np₀ +ℕ Nq₀) +ℕ Np) Nq)
    Nq≤N : Nq ≤ℕ ((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq
    Nq≤N = NatP.m≤n+m Nq ((Np₀ +ℕ Nq₀) +ℕ Np)
    Np₀≤n : Np₀ ≤ℕ n
    Np₀≤n = NatP.≤-trans Np₀≤N N≤n
    Nq₀≤n : Nq₀ ≤ℕ n
    Nq₀≤n = NatP.≤-trans Nq₀≤N N≤n
    Np≤n : Np ≤ℕ n
    Np≤n = NatP.≤-trans Np≤N N≤n
    Nq≤n : Nq ≤ℕ n
    Nq≤n = NatP.≤-trans Nq≤N N≤n
  in ≤-trans (partial-mul-≤ p q 0≤p 0≤q n)
       (le-self-add {p = expPartial (p + q) (n +ℕ n)} (<⇒≤ 0<d))
   , ≤-trans (partial-mul-upper p q 0≤p 0≤q n)
       (≤-trans (≤-of-≡ _ _
                   (+-assoc (expPartial p n * expPartial q n)
                            (expPartial p n * tail q n)
                            (tail p n * expPartial q n)))
         (+-mono-≤ (≤-refl {expPartial p n * expPartial q n})
                   (corr-≤′ p q 0≤p 0≤q d Np₀ Nq₀ Np Nq j
                            brp₀ brq₀ brp brq shrink n
                            Np₀≤n Nq₀≤n Np≤n Nq≤n)))

------------------------------------------------------------------------
-- The product is close to the doubled sum
--
-- 乘积与倍长和彼此接近

-- Every rational tolerance is met by the two truncations once the index
-- passes a bound: the product of the partial sums and the doubled
-- partial sum at the summed parameter are within `d` of each other.
--
-- 只要指标越过某个界，两个截断就满足任意有理容差：部分和之积与参数之和处倍长
-- 的部分和彼此相差不超过 `d`。
expPartial-add-close :
  (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
  → Σ ℕ (λ N → ∀ n → N ≤ℕ n
      → (expPartial p n * expPartial q n
           ≤ expPartial (p + q) (n +ℕ n) + d)
        × (expPartial (p + q) (n +ℕ n)
           ≤ expPartial p n * expPartial q n + d))
expPartial-add-close p q 0≤p 0≤q d 0<d =
  let
    -- The square geometry is bounded by the two brackets at tolerance one.
    --
    -- 平方几何由容差一处的两个括号界定。
    Np₀ , brp₀ = exp-bracket p 0≤p 1ℚ 0<1
    Nq₀ , brq₀ = exp-bracket q 0≤q 1ℚ 0<1
    Gp : ℚ
    Gp = expPartial p Np₀ + 1ℚ
    Gq : ℚ
    Gq = expPartial q Nq₀ + 1ℚ
    G : ℚ
    G = Gp + Gq
    0≤Gp : 0ℚ ≤ Gp
    0≤Gp = plus1-nonNeg (expPartial p Np₀) (partial-nonNeg p 0≤p Np₀)
    0≤Gq : 0ℚ ≤ Gq
    0≤Gq = plus1-nonNeg (expPartial q Nq₀) (partial-nonNeg q 0≤q Nq₀)
    0≤G : 0ℚ ≤ G
    0≤G = add-nonNeg Gp Gq 0≤Gp 0≤Gq
    j , shrink = rat-shrink G 0≤G d 0<d
    -- The two tails are read off the brackets at tolerance `ε j`.
    --
    -- 两条尾部由容差 `ε j` 处的括号读出。
    Np , brp = exp-bracket p 0≤p (ε j) (0<ε j)
    Nq , brq = exp-bracket q 0≤q (ε j) (0<ε j)
  in ((Np₀ +ℕ Nq₀) +ℕ Np) +ℕ Nq
   , λ n N≤n →
       half′ p q 0≤p 0≤q d 0<d Np₀ Nq₀ Np Nq j
             (λ k → proj₂ (brp₀ k))
             (λ k → proj₂ (brq₀ k))
             (λ k → proj₂ (brp k))
             (λ k → proj₂ (brq k))
             shrink n N≤n

------------------------------------------------------------------------
-- Rational layer bounds for the square-root construction
--
-- 平方根构造用的有理层界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Sqrt.Bounds where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (≤-total)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; positive; nonNegative)
open import Data.Rational.Base using (-_; 1/_; Positive)
open import Data.Rational.Properties using
  (≤-reflexive; ≤-refl; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; +-mono-≤; +-monoʳ-<
  ; +-monoˡ-<; +-comm; +-identityˡ; +-identityʳ; <-irrefl; <-trans
  ; *-monoˡ-≤-nonNeg; *-monoˡ-<-pos; neg-antimono-<; <-cmp; +-inverseʳ; *-comm
  ; *-assoc; *-identityʳ; *-distribˡ-+; +-assoc; pos⇒nonZero; 1/pos⇒pos
  ; pos*pos⇒pos; positive⁻¹; *-inverseˡ; +-inverseˡ; pos⇒nonNeg)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; subst; subst₂; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (¬_)

open import Base.RationalRing using (sq+)
open import Real using (embed; 0<embed)
open import Real.IntervalEquiv using (node; l; u; l-mono; u-mono)
open import Real.Interval using (RealI; embedℚ; δ; δ-pos)
open import Real.Interval.Mul.Order using (δ-below; δ-mono)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.Rational using (pos-diff; plus-diff)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- Rational endpoints
--
-- 有理端点

negδ-add-lt : (q : ℚ) (n : ℕ) → (- δ n) + q < q
negδ-add-lt q n =
  subst₂ _<_
    (+-comm q (- δ n))
    (+-identityʳ q)
    (+-monoʳ-< q (neg-antimono-< (δ-pos n)))

-- Adding the dyadic tolerance keeps q above q.
--
-- 加上二进容差不会把 q 降下来。
δ-add-≤ : (q : ℚ) (n : ℕ) → q ≤ δ n + q
δ-add-≤ q n =
  ≤-trans (≤-reflexive (sym (+-identityˡ q)))
          (+-mono-≤ (<⇒≤ (δ-pos n)) (≤-refl {q}))

-- Case split on the comparison of two naturals.
--
-- 对两个自然数的大小关系做分案。
≤-total-elim : {A : Set} {m n : ℕ} →
  (m ≤ℕ n → A) → (n ≤ℕ m → A) → A
≤-total-elim {m = m} {n = n} f g = [ f , g ] (≤-total m n)

-- The lower endpoint of a layer is below the real.
--
-- 任意层的下端点在实数之下。
l-layer-≤ : (y : RealI) (k : ℕ) → embedℚ (l y k) ≤ℝ y
l-layer-≤ y k (n , h) = contradiction
  where
  h' : u y n < (- δ n) + l y k
  h' = subst (λ z → u y n < z) (l-dyadic (l y k) n) h

  u<lk : u y n < l y k
  u<lk = <-≤-trans h' (<⇒≤ (negδ-add-lt (l y k) n))

  lo-at : (m : ℕ) → l y m < u y m
  lo-at m = RealI.lo (node y m)

  case-k≤n : k ≤ℕ n → u y n < u y n
  case-k≤n k≤n =
    <-≤-trans (<-≤-trans u<lk (l-mono y k≤n)) (<⇒≤ (lo-at n))

  case-n≤k : n ≤ℕ k → u y n < u y n
  case-n≤k n≤k =
    <-≤-trans (<-≤-trans u<lk (<⇒≤ (lo-at k))) (u-mono y n≤k)

  u<u : u y n < u y n
  u<u = ≤-total-elim {A = u y n < u y n} case-k≤n case-n≤k

  contradiction : ⊥
  contradiction = <-irrefl refl u<u

-- The upper endpoint of a layer is above the real.
--
-- 任意层的上端点在实数之上。
u-layer-≤ : (y : RealI) (k : ℕ) → y ≤ℝ embedℚ (u y k)
u-layer-≤ y k (n , h) = contradiction
  where
  h' : δ n + u y k < l y n
  h' = subst (λ z → z < l y n) (u-dyadic (u y k) n) h

  lo-at : (m : ℕ) → l y m < u y m
  lo-at m = RealI.lo (node y m)

  case-k≤n : k ≤ℕ n → (δ n + u y k) < (δ n + u y k)
  case-k≤n k≤n =
    <-≤-trans (<-≤-trans h' (<⇒≤ (lo-at n)))
              (≤-trans (u-mono y k≤n) (δ-add-≤ (u y k) n))

  case-n≤k : n ≤ℕ k → (δ n + u y k) < (δ n + u y k)
  case-n≤k n≤k =
    <-≤-trans (<-≤-trans h' (l-mono y n≤k))
              (<⇒≤ (<-≤-trans (lo-at k) (δ-add-≤ (u y k) n)))

  bad : (δ n + u y k) < (δ n + u y k)
  bad = ≤-total-elim {A = (δ n + u y k) < (δ n + u y k)} case-k≤n case-n≤k

  contradiction : ⊥
  contradiction = <-irrefl refl bad

------------------------------------------------------------------------
-- Strict monotonicity of squaring on non-negative rationals
--
-- 非负有理数上平方的严格单调性

sq-< : (p q : ℚ) → 0ℚ ≤ p → p < q → p * p < q * q
sq-< p q 0≤p p<q = ≤-<-trans p*p≤p*q p*q<q*q
  where
  0<q : 0ℚ < q
  0<q = ≤-<-trans 0≤p p<q

  p*p≤p*q : p * p ≤ p * q
  p*p≤p*q = *-monoˡ-≤-nonNeg p {{nonNegative 0≤p}} (<⇒≤ p<q)

  p*q<q*q : p * q < q * q
  p*q<q*q = *-monoˡ-<-pos q {{positive 0<q}} p<q

------------------------------------------------------------------------
-- Deciding a rational square against a layer endpoint
--
-- 有理平方与层端点的判决

-- Either p * p is below the k-th lower endpoint of y, or it is not.
--
-- 要么 p * p 低于 y 的第 k 层下端点，要么不是。
decide-below : (y : RealI) (k : ℕ) (p : ℚ) →
  (p * p < l y k) ⊎ (¬ (p * p < l y k))
decide-below y k p with <-cmp (p * p) (l y k)
... | tri< lt _ _   = inj₁ lt
... | tri≈ ¬lt _ _ = inj₂ ¬lt
... | tri> ¬lt _ _ = inj₂ ¬lt

------------------------------------------------------------------------
-- Positivity of a difference, and of the square gap
--
-- 差与平方差的正当性

-- A non-negative number whose square is below a positive square is
-- itself below it.
--
-- 非负数若其平方低于一个正数的平方，则它低于该正数。
sq-gap-pos : (u q : ℚ) → 0ℚ ≤ u → 0ℚ < q → u * u < q * q → 0ℚ < q - u
sq-gap-pos u q 0≤u 0<q uu<qq with <-cmp u q
... | tri< u<q _ _   = pos-diff u q u<q
... | tri≈ _ u≡q _   = ⊥-elim (<-irrefl refl
                           (subst (λ z → u * u < z * z) (sym u≡q) uu<qq))
... | tri> _ _ q<u   =
  ⊥-elim (<-irrefl refl (<-trans qq<uu uu<qq))
  where
  qq<uu : q * q < u * u
  qq<uu = sq-< q u (<⇒≤ 0<q) q<u

------------------------------------------------------------------------
-- Difference algebra
--
-- 差代数


-- A bound below a difference transfers to the minuend.
--
-- 低于某个差的界可以转移到被减数上。
sub-lt-swap : (u d q : ℚ) → d < q - u → u < - d + q
sub-lt-swap u d q d<q-u = subst₂ _<_ lhs≡ rhs≡ step₂
  where
  q-u+u≡q : (q - u) + u ≡ q
  q-u+u≡q = begin
    (q - u) + u
      ≡⟨ +-assoc q (- u) u ⟩
    q + ((- u) + u)
      ≡⟨ cong (λ z → q + z) (+-inverseˡ u) ⟩
    q + 0ℚ
      ≡⟨ +-identityʳ q ⟩
    q
      ∎

  step₁ : u + d < q
  step₁ = subst₂ _<_
            (+-comm d u)
            q-u+u≡q
            (+-monoˡ-< u d<q-u)

  lhs≡ : (u + d) + (- d) ≡ u
  lhs≡ = begin
    (u + d) + (- d)
      ≡⟨ +-assoc u d (- d) ⟩
    u + (d + (- d))
      ≡⟨ cong (λ z → u + z) (+-inverseʳ d) ⟩
    u + 0ℚ
      ≡⟨ +-identityʳ u ⟩
    u
      ∎

  rhs≡ : q + (- d) ≡ - d + q
  rhs≡ = +-comm q (- d)

  step₂ : (u + d) + (- d) < q + (- d)
  step₂ = +-monoˡ-< (- d) step₁

------------------------------------------------------------------------
-- Reflection of strict order through the rational embedding
--
-- 严格序经有理嵌入的反射

-- If one embedded rational lies strictly below another, so does the
-- rational itself.
--
-- 两个有理数的嵌入若严格有序，则有理数本身亦然。
embedℚ-reflect : (p t : ℚ) → embedℚ p <ℝ embedℚ t → p < t
embedℚ-reflect p t (n , h) = <-trans p<δp (<-trans h' negδt<t)
  where
  h' : δ n + p < (- δ n) + t
  h' = subst₂ _<_ (u-dyadic p n) (l-dyadic t n) h

  p<δp : p < δ n + p
  p<δp = subst₂ _<_
           (+-identityʳ p)
           (+-comm p (δ n))
           (+-monoʳ-< p (δ-pos n))

  negδt<t : (- δ n) + t < t
  negδt<t = negδ-add-lt t n

------------------------------------------------------------------------
-- Non-strict monotonicity of the rational embedding
--
-- 有理嵌入的非严格单调性

embedℚ-≤ : (p t : ℚ) → p ≤ t → embedℚ p ≤ℝ embedℚ t
embedℚ-≤ p t p≤t emb< =
  <-irrefl {x = p} {y = p} refl
    (≤-<-trans p≤t (embedℚ-reflect t p emb<))

------------------------------------------------------------------------
-- Widening a square bound by a small rational step
--
-- 平方界的有理小幅外扩

-- A non-negative rational whose square lies below s can be moved a
-- little to the right while keeping its square below s.
--
-- 非负有理数的平方若低于 s，则可以向右微移而平方仍低于 s。
sq-widen : (p s : ℚ) → 0ℚ ≤ p → p * p < s
         → Σ ℚ (λ r → p < r × r * r < s)
sq-widen p s 0≤p pp<s = r , p<r , rr<s
  where
  d : ℚ
  d = s - p * p

  0<d : 0ℚ < d
  0<d = pos-diff (p * p) s pp<s

  0≤p+p : 0ℚ ≤ p + p
  0≤p+p = subst (λ z → z ≤ p + p) (+-identityˡ 0ℚ) (+-mono-≤ 0≤p 0≤p)

  e : ℚ
  e = embed 1

  0<e : 0ℚ < e
  0<e = 0<embed 0

  two : ℚ
  two = e + e

  e<two : e < two
  e<two = subst (λ z → z < e + e) (+-identityʳ e)
            (+-monoʳ-< e 0<e)

  0<two : 0ℚ < two
  0<two = ≤-<-trans (<⇒≤ 0<e) e<two

  c : ℚ
  c = (p + p) + two

  pp<c : p + p < c
  pp<c = subst (λ z → z < (p + p) + two) (+-identityʳ (p + p))
           (+-monoʳ-< (p + p) 0<two)

  0<c : 0ℚ < c
  0<c = ≤-<-trans 0≤p+p pp<c

  invc : ℚ
  invc = (1/ c) {{pos⇒nonZero c {{positive 0<c}}}}

  pos-invc : Positive invc
  pos-invc = 1/pos⇒pos c {{positive 0<c}}

  g : ℚ
  g = d * invc

  0<g : 0ℚ < g
  0<g = positive⁻¹ g {{pos*pos⇒pos d {{positive 0<d}} invc {{pos-invc}}}}

  probe₁ : Σ ℕ (λ m → 0 ≤ℕ m × δ m < g)
  probe₁ = δ-below g 0<g 0

  m₁ : ℕ
  m₁ = proj₁ probe₁

  h₁<g : δ m₁ < g
  h₁<g = proj₂ (proj₂ probe₁)

  probe₂ : Σ ℕ (λ m → m₁ ≤ℕ m × δ m < two)
  probe₂ = δ-below two 0<two m₁

  m₂ : ℕ
  m₂ = proj₁ probe₂

  m₁≤m₂ : m₁ ≤ℕ m₂
  m₁≤m₂ = proj₁ (proj₂ probe₂)

  h₂<two : δ m₂ < two
  h₂<two = proj₂ (proj₂ probe₂)

  h : ℚ
  h = δ m₂

  0<h : 0ℚ < h
  0<h = δ-pos m₂

  h<g : h < g
  h<g = ≤-<-trans (δ-mono m₁≤m₂) h₁<g

  h≤two : h ≤ two
  h≤two = <⇒≤ h₂<two

  r : ℚ
  r = p + h

  p<r : p < r
  p<r = subst (λ z → z < p + h) (+-identityʳ p) (+-monoʳ-< p 0<h)

  hh≤ : h * h ≤ h * two
  hh≤ = *-monoˡ-≤-nonNeg h {{pos⇒nonNeg h {{positive 0<h}}}} h≤two

  htwo : h * two ≡ h + h
  htwo = begin
    h * two
      ≡⟨ *-distribˡ-+ h e e ⟩
    h * e + h * e
      ≡⟨ cong₂ _+_ (*-identityʳ h) (*-identityʳ h) ⟩
    h + h
      ∎

  hc : h * c ≡ (p * h + p * h) + (h + h)
  hc = begin
    h * c
      ≡⟨⟩
    h * ((p + p) + two)
      ≡⟨ *-distribˡ-+ h (p + p) two ⟩
    h * (p + p) + h * two
      ≡⟨ cong₂ _+_ (*-distribˡ-+ h p p) htwo ⟩
    (h * p + h * p) + (h + h)
      ≡⟨ cong₂ _+_ (cong₂ _+_ (*-comm h p) (*-comm h p)) refl ⟩
    (p * h + p * h) + (h + h)
      ∎

  shift≤ : h * h + (p * h + p * h) ≤ h * c
  shift≤ =
    ≤-trans
      (+-mono-≤ hh≤ (≤-refl {p * h + p * h}))
      (≤-trans
        (≤-reflexive (cong (λ z → z + (p * h + p * h)) htwo))
        (≤-trans
          (≤-reflexive (+-comm (h + h) (p * h + p * h)))
          (≤-reflexive (sym hc))))

  sq≤ : (p + h) * (p + h) ≤ p * p + h * c
  sq≤ = ≤-trans (≤-reflexive (sq+ p h))
          (+-mono-≤ (≤-refl {p * p}) shift≤)

  gc≡d : g * c ≡ d
  gc≡d = begin
    g * c
      ≡⟨⟩
    (d * invc) * c
      ≡⟨ *-assoc d invc c ⟩
    d * (invc * c)
      ≡⟨ cong (λ z → d * z)
           (*-inverseˡ c {{pos⇒nonZero c {{positive 0<c}}}}) ⟩
    d * 1ℚ
      ≡⟨ *-identityʳ d ⟩
    d
      ∎

  hc<d : h * c < d
  hc<d = subst (λ z → h * c < z) gc≡d
           (*-monoˡ-<-pos c {{positive 0<c}} h<g)

  p2d<s : p * p + h * c < s
  p2d<s = subst (λ z → p * p + h * c < z) (plus-diff (p * p) s)
            (+-monoʳ-< (p * p) hc<d)

  rr<s : r * r < s
  rr<s = ≤-<-trans sq≤ p2d<s

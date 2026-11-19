------------------------------------------------------------------------
-- Bounds and the sum algebra behind them
--
-- 界及其背后的求和代数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Lipschitz where

open import Data.Nat as Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _*_)
open import Data.Rational.Base using (1/_; positive; Positive; nonNegative)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; +-identityˡ; +-identityʳ; +-assoc; +-monoˡ-≤
  ; +-monoʳ-≤; 1/pos⇒pos; pos⇒nonZero; positive⁻¹; +-comm
  ; *-zeroʳ; *-identityʳ; *-assoc; *-comm; *-inverseˡ; *-inverseʳ; *-distribˡ-+
  ; *-distribʳ-+; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (+interchange; 0≤1)
open import Real using (embed; 0<embed; embed-+-hom)
open import Real.Interval.Exp.Core as ExpCore using
  (term; term-suc; term-nonNeg; expPartial; sumQ-mono; div-suc-nonNeg
  ; sucNonZero; sumQ; _≤ℕ_)
open import Real.Interval.Exp.Order using (term-one)
open import Real.Interval.Series.Bounds using (le-self-add)
open import Real.Interval.Node using (mul-nonNeg; add2-nonNeg)

------------------------------------------------------------------------
-- L7: ℚ-level Lipschitz and the global bound for expPartial
--
-- L7：ℚ 层 Lipschitz 与 expPartial 的整体界

le-add-right : (a b : ℚ) (0≤b : 0ℚ ≤ b) → a ≤ a + b
le-add-right a b 0≤b = le-self-add {a} {b} 0≤b

prod-nonNeg : (a b : ℚ) (0≤a : 0ℚ ≤ a) (0≤b : 0ℚ ≤ b) → 0ℚ ≤ a * b
prod-nonNeg a b 0≤a 0≤b = mul-nonNeg {a} {b} 0≤a 0≤b

sum-nonNegℚ : (a b : ℚ) (0≤a : 0ℚ ≤ a) (0≤b : 0ℚ ≤ b) → 0ℚ ≤ a + b
sum-nonNegℚ a b 0≤a 0≤b = add2-nonNeg {a} {b} 0≤a 0≤b

inv-nonNeg : (z : ℚ) (P : Positive z) → 0ℚ ≤ 1/_ z {{pos⇒nonZero z {{P}}}}
inv-nonNeg z P =
  <⇒≤ (positive⁻¹ (1/_ z {{pos⇒nonZero z {{P}}}}) {{1/pos⇒pos z {{P}}}})

------------------------------------------------------------------------
-- embed 1 = 1
--
-- embed 1 = 1（嵌入保 1）

embed-1 : embed (suc zero) ≡ 1ℚ
embed-1 = refl

nat-suc-eq : (k : ℕ) → suc k +ℕ 1 ≡ suc (suc k)
nat-suc-eq k = trans (NatP.+-suc (suc k) zero) (cong suc (NatP.+-identityʳ (suc k)))

embed-suc-eq : (k : ℕ) → embed (suc (suc k)) ≡ embed (suc k) + 1ℚ
embed-suc-eq k =
  trans (sym (cong embed (nat-suc-eq k)))
    (trans (embed-+-hom (suc k) 1) (cong (λ z → embed (suc k) + z) embed-1))

------------------------------------------------------------------------
-- (x * E) / E = x
--
-- （x * E）/ E = x（乘逆元相消）

div-cancel : (x : ℚ) (k : ℕ)
           → (x * embed (suc k)) * (1/_ (embed (suc k)) {{sucNonZero k}}) ≡ x
div-cancel x k =
  let E = embed (suc k)
      nz = sucNonZero k
      e1 : E * (1/_ E {{nz}}) ≡ 1ℚ
      e1 = *-inverseʳ E {{nz}}
  in begin
    (x * E) * (1/_ E {{nz}})
      ≡⟨ *-assoc x E (1/_ E {{nz}}) ⟩
    x * (E * (1/_ E {{nz}}))
      ≡⟨ cong (λ z → x * z) e1 ⟩
    x * 1ℚ
      ≡⟨ *-identityʳ x ⟩
    x
      ∎

------------------------------------------------------------------------
-- Stepping the denominator back: term q (k+1) * (k+1) = term q k * q
--
-- 分母回退：term q (k+1) * (k+1) = term q k * q

term-mul : (q : ℚ) (k : ℕ) → term q (suc k) * embed (suc k) ≡ term q k * q
term-mul q k =
  let E = embed (suc k)
      nz = sucNonZero k
      inv = 1/_ E {{nz}}
      e1 : inv * E ≡ 1ℚ
      e1 = *-inverseˡ E {{nz}}
  in begin
    term q (suc k) * E
      ≡⟨ cong (λ z → z * E) (term-suc q k) ⟩
    (term q k * (q * inv)) * E
      ≡⟨ *-assoc (term q k) (q * inv) E ⟩
    term q k * ((q * inv) * E)
      ≡⟨ cong (λ z → term q k * z) (*-assoc q inv E) ⟩
    term q k * (q * (inv * E))
      ≡⟨ cong (λ z → term q k * (q * z)) e1 ⟩
    term q k * (q * 1ℚ)
      ≡⟨ cong (λ z → term q k * z) (*-identityʳ q) ⟩
    term q k * q
      ∎

------------------------------------------------------------------------
-- one-step Lipschitz bound for the summands
--
-- 单项的一步 Lipschitz 界

-- term (q+h) (k+1) is obtained from term (q+h) k by dividing by k+1; the
-- increment over the same step for q is absorbed by h times the *next*
-- summand term (q+h) k. Everything is at the level of ℚ; the h-factor
-- survives into the partial sums, which is the shape the locatedness
-- argument of log needs.
--
-- term (q+h) (k+1) 由 term (q+h) k 除 (k+1) 得到；相对 q 的同一步增量
-- 被 h 乘以下一项 term (q+h) k 吸收。全部在 ℚ 层，h 因子保留到部分和，
-- 正是 log 的 locatedness 论证所需的形状。
term-lip-suc : (q h : ℚ) (0≤q : 0ℚ ≤ q) (0≤h : 0ℚ ≤ h) (k : ℕ)
             → term (q + h) (suc k) ≤ term q (suc k) + h * term (q + h) k
term-lip-suc q h 0≤q 0≤h zero =
  let r1 : term (q + h) (suc zero) ≡ q + h
      r1 = term-one (q + h)
      q1 : term q (suc zero) ≡ q
      q1 = term-one q
      h1 : h * term (q + h) zero ≡ h
      h1 = *-identityʳ h
      rhs : term q (suc zero) + h * term (q + h) zero ≡ q + h
      rhs = cong₂ _+_ q1 h1
  in subst₂ (λ a b → a ≤ b) (sym r1) (sym rhs) (≤-refl {q + h})
term-lip-suc q h 0≤q 0≤h (suc k) =
  let r = q + h
      0≤r : 0ℚ ≤ r
      0≤r = sum-nonNegℚ q h 0≤q 0≤h
      E : ℚ
      E = embed (suc (suc k))
      E₁ : ℚ
      E₁ = embed (suc k)
      inv : ℚ
      inv = 1/_ E {{sucNonZero (suc k)}}
      Ar : ℚ
      Ar = term r (suc k)
      Aq : ℚ
      Aq = term q (suc k)
      Ar' : ℚ
      Ar' = term r k
      0≤Ar' : 0ℚ ≤ Ar'
      0≤Ar' = term-nonNeg r 0≤r k
      0≤inv : 0ℚ ≤ inv
      0≤inv = inv-nonNeg E (positive (0<embed (suc k)))
      IH : Ar ≤ Aq + h * Ar'
      IH = term-lip-suc q h 0≤q 0≤h k
      0≤qinv : 0ℚ ≤ q * inv
      0≤qinv = div-suc-nonNeg q 0≤q (suc k)
      mono-q : Ar * (q * inv) ≤ (Aq + h * Ar') * (q * inv)
      mono-q = *-monoʳ-≤-nonNeg (q * inv) {{nonNegative 0≤qinv}} IH
      dist-A : (Aq + h * Ar') * (q * inv) ≡ Aq * (q * inv) + (h * Ar') * (q * inv)
      dist-A = *-distribʳ-+ (q * inv) Aq (h * Ar')
      step-A : Ar * (q * inv) ≤ Aq * (q * inv) + (h * Ar') * (q * inv)
      step-A = subst (λ z → Ar * (q * inv) ≤ z) dist-A mono-q
      rd : r * inv ≡ q * inv + h * inv
      rd = *-distribʳ-+ inv q h
      split-r : Ar * (r * inv) ≡ Ar * (q * inv) + Ar * (h * inv)
      split-r = trans (cong (λ z → Ar * z) rd) (*-distribˡ-+ Ar (q * inv) (h * inv))
      0≤Arh : 0ℚ ≤ Ar' * h
      0≤Arh = prod-nonNeg Ar' h 0≤Ar' 0≤h
      E-suc : E ≡ E₁ + 1ℚ
      E-suc = embed-suc-eq k
      ArE₁ : Ar * E₁ ≡ Ar' * r
      ArE₁ = term-mul r k
      Ar'r : Ar' * r ≡ Ar' * q + Ar' * h
      Ar'r = *-distribˡ-+ Ar' q h
      ArE : Ar * E ≡ (Ar' * q + Ar' * h) + Ar
      ArE =
        trans (cong (λ z → Ar * z) E-suc)
          (trans (*-distribˡ-+ Ar E₁ 1ℚ)
            (trans (cong (λ z → Ar * E₁ + z) (*-identityʳ Ar))
              (trans (cong (λ z → z + Ar) ArE₁)
                (cong (λ z → z + Ar) Ar'r))))
      sum-shift : (Ar' * q + Ar) + Ar' * h ≡ (Ar' * q + Ar' * h) + Ar
      sum-shift =
        trans (+-assoc (Ar' * q) Ar (Ar' * h))
          (trans (cong (λ z → (Ar' * q) + z) (+-comm Ar (Ar' * h)))
                 (sym (+-assoc (Ar' * q) (Ar' * h) Ar)))
      sum-le : Ar' * q + Ar ≤ Ar * E
      sum-le =
        subst (λ z → Ar' * q + Ar ≤ z) (sym ArE)
          (subst (λ z → Ar' * q + Ar ≤ z) sum-shift
            (le-add-right (Ar' * q + Ar) (Ar' * h) 0≤Arh))
      cA : (h * Ar') * (q * inv) ≡ h * ((Ar' * q) * inv)
      cA = trans (*-assoc h Ar' (q * inv))
             (cong (λ z → h * z) (sym (*-assoc Ar' q inv)))
      cC : Ar * (h * inv) ≡ h * (Ar * inv)
      cC = trans (sym (*-assoc Ar h inv))
             (trans (cong (λ z → z * inv) (*-comm Ar h))
                    (*-assoc h Ar inv))
      cD : h * ((Ar' * q) * inv) + h * (Ar * inv) ≡ h * ((Ar' * q) * inv + Ar * inv)
      cD = sym (*-distribˡ-+ h ((Ar' * q) * inv) (Ar * inv))
      cE : (Ar' * q) * inv + Ar * inv ≡ (Ar' * q + Ar) * inv
      cE = sym (*-distribʳ-+ inv (Ar' * q) Ar)
      key-eq : (h * Ar') * (q * inv) + Ar * (h * inv) ≡ h * ((Ar' * q + Ar) * inv)
      key-eq = trans (cong₂ _+_ cA cC) (trans cD (cong (λ z → h * z) cE))
      key-ineq : (Ar' * q + Ar) * inv ≤ (Ar * E) * inv
      key-ineq = *-monoʳ-≤-nonNeg inv {{nonNegative 0≤inv}} sum-le
      inner : (Ar' * q + Ar) * inv ≤ Ar
      inner = subst (λ z → (Ar' * q + Ar) * inv ≤ z) (div-cancel Ar (suc k)) key-ineq
      h-inner : h * ((Ar' * q + Ar) * inv) ≤ h * Ar
      h-inner = *-monoˡ-≤-nonNeg h {{nonNegative 0≤h}} inner
      key-bound : (h * Ar') * (q * inv) + Ar * (h * inv) ≤ h * Ar
      key-bound = subst (λ z → z ≤ h * Ar) (sym key-eq) h-inner
      chain-1 : Ar * (q * inv) + Ar * (h * inv)
              ≤ (Aq * (q * inv) + (h * Ar') * (q * inv)) + Ar * (h * inv)
      chain-1 = +-monoˡ-≤ (Ar * (h * inv)) step-A
      chain-2 : (Aq * (q * inv) + (h * Ar') * (q * inv)) + Ar * (h * inv)
              ≤ Aq * (q * inv) + h * Ar
      chain-2 =
        subst (λ z → z ≤ Aq * (q * inv) + h * Ar)
          (sym (+-assoc (Aq * (q * inv)) ((h * Ar') * (q * inv)) (Ar * (h * inv))))
          (+-monoʳ-≤ (Aq * (q * inv)) key-bound)
      c1 : Ar * (r * inv)
         ≤ (Aq * (q * inv) + (h * Ar') * (q * inv)) + Ar * (h * inv)
      c1 = subst (λ z → z ≤ (Aq * (q * inv) + (h * Ar') * (q * inv)) + Ar * (h * inv))
           (sym split-r) chain-1
  in ≤-trans c1 chain-2

------------------------------------------------------------------------
-- Lipschitz bound for every summand, uniformly in the index
--
-- 对每个下标一致的单项 Lipschitz 界

term-lip : (q h : ℚ) (0≤q : 0ℚ ≤ q) (0≤h : 0ℚ ≤ h) (n : ℕ)
         → term (q + h) n ≤ term q n + h * term (q + h) (n ∸ 1)
term-lip q h 0≤q 0≤h zero =
  subst (λ z → 1ℚ ≤ 1ℚ + z) (sym (*-identityʳ h)) (le-add-right 1ℚ h 0≤h)
term-lip q h 0≤q 0≤h (suc n) = term-lip-suc q h 0≤q 0≤h n

------------------------------------------------------------------------
-- a uniform rational bound for the whole partial-sum sequence
--
-- 部分和序列的整体有理上界

expPartial-bound : (q : ℚ) (0≤q : 0ℚ ≤ q) (d : ℚ) (0<d : 0ℚ < d)
                 → Σ ℚ (λ B → ∀ n → expPartial q n ≤ B)
expPartial-bound q 0≤q d 0<d =
  let N , _ , lower = ExpCore.exp-bracket-le q 0≤q d 0<d
      B = expPartial q N + d
  in B , goal N lower
  where
  goal : (N : ℕ)
       → (∀ m → N ≤ℕ m → expPartial q m ≤ expPartial q N + d)
       → ∀ n → expPartial q n ≤ expPartial q N + d
  goal N lower n with NatP.≤-total n N
  ... | inj₁ n≤N = ≤-trans (ExpCore.expPartial-le q 0≤q n N n≤N)
                     (le-add-right (expPartial q N) d (<⇒≤ 0<d))
  ... | inj₂ N≤n = lower n N≤n

------------------------------------------------------------------------
-- L8: additivity of sumQ, constant extraction, and parametric Lipschitz
--
-- L8：sumQ 可加性、常数提取与参数方向 Lipschitz

sumQ-add : (a b : ℕ → ℚ) (n : ℕ)
         → sumQ (λ i → a i + b i) n ≡ sumQ a n + sumQ b n
sumQ-add a b zero = sym (+-identityˡ 0ℚ)
sumQ-add a b (suc n) =
  trans (cong (λ z → z + (a n + b n)) (sumQ-add a b n))
        (+interchange (sumQ a n) (sumQ b n) (a n) (b n))

------------------------------------------------------------------------
-- sumQ pulls out a constant factor
--
-- sumQ 提取常数因子

sumQ-scale : (c : ℚ) (a : ℕ → ℚ) (n : ℕ)
           → sumQ (λ i → c * a i) n ≡ c * sumQ a n
sumQ-scale c a zero = sym (*-zeroʳ c)
sumQ-scale c a (suc n) =
  trans (cong (λ z → z + c * a n) (sumQ-scale c a n))
        (sym (*-distribˡ-+ c (sumQ a n) (a n)))

------------------------------------------------------------------------
-- The shifted sum agrees with the partial sum
--
-- 平移后的和与部分和一致

shift-sum-eq : (r : ℚ) (m : ℕ)
             → sumQ (λ i → term r (i ∸ 1)) (suc m) ≡ 1ℚ + expPartial r m
shift-sum-eq r zero = trans (+-identityˡ 1ℚ) (sym (+-identityʳ 1ℚ))
shift-sum-eq r (suc m) =
  trans (cong (λ z → z + term r m) (shift-sum-eq r m))
        (+-assoc 1ℚ (expPartial r m) (term r m))

------------------------------------------------------------------------
-- Parameter direction Lipschitz for the partial sums
--
-- 部分和对参数方向的 Lipschitz 性

-- The difference is controlled by h times the bound for the shifted sum.
--
-- 参数方向的 Lipschitz（对部分和）：差由 h 乘移位和的上界控制。
expPartial-param-lip : (p h : ℚ) (0≤p : 0ℚ ≤ p) (0≤h : 0ℚ ≤ h)
                       (n : ℕ) (C : ℚ)
                       (sumB : ∀ m → sumQ (λ i → term (p + h) (i ∸ 1)) m ≤ C)
                     → expPartial (p + h) n ≤ expPartial p n + h * C
expPartial-param-lip p h 0≤p 0≤h n C sumB =
  let f = term (p + h)
      g = λ i → term p i + h * term (p + h) (i ∸ 1)
      step1 : expPartial (p + h) n ≤ sumQ g n
      step1 = sumQ-mono f g (λ i → term-lip p h 0≤p 0≤h i) n
      step2 : sumQ g n ≡ expPartial p n + h * sumQ (λ i → term (p + h) (i ∸ 1)) n
      step2 =
        trans (sumQ-add (term p) (λ i → h * term (p + h) (i ∸ 1)) n)
              (cong (λ z → sumQ (term p) n + z)
                    (sumQ-scale h (λ i → term (p + h) (i ∸ 1)) n))
      step3 : expPartial p n + h * sumQ (λ i → term (p + h) (i ∸ 1)) n
            ≤ expPartial p n + h * C
      step3 = +-monoʳ-≤ (expPartial p n)
                (*-monoˡ-≤-nonNeg h {{nonNegative 0≤h}} (sumB n))
  in ≤-trans step1
       (subst (λ z → z ≤ expPartial p n + h * C) (sym step2) step3)

------------------------------------------------------------------------
-- 0 ≤ 1 and the shift-sum bound from a global bound
--
-- 0 ≤ 1，以及由整体界得到移位和的上界

shift-sum-bnd : (r : ℚ) (C : ℚ) (bnd : ∀ j → expPartial r j ≤ C) (m : ℕ)
              → sumQ (λ i → term r (i ∸ 1)) m ≤ 1ℚ + C
shift-sum-bnd r C bnd zero = ≤-trans 0≤1 (le-add-right 1ℚ C (bnd zero))
shift-sum-bnd r C bnd (suc m) =
  subst (λ z → z ≤ 1ℚ + C) (sym (shift-sum-eq r m))
        (+-monoʳ-≤ 1ℚ (bnd m))

expPartial-param-bnd : (p h : ℚ) (0≤p : 0ℚ ≤ p) (0≤h : 0ℚ ≤ h)
                       (n : ℕ) (C : ℚ) (bnd : ∀ j → expPartial (p + h) j ≤ C)
                     → expPartial (p + h) n ≤ expPartial p n + h * (1ℚ + C)
expPartial-param-bnd p h 0≤p 0≤h n C bnd =
  expPartial-param-lip p h 0≤p 0≤h n (1ℚ + C) (shift-sum-bnd (p + h) C bnd)

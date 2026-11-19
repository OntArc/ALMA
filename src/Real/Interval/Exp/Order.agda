------------------------------------------------------------------------
-- Monotonicity and strict monotonicity of expq
--
-- expq 的单调性与严格单调性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.Order where

open import Data.Empty using (⊥-elim)
open import Data.Nat as Nat using (ℕ; zero; suc; _^_) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NatP
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; _*_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Base using (_÷_; 1/_; positive)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; <-≤-trans; <-trans; <-asym; +-mono-≤; +-monoˡ-<
  ; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-assoc; +-monoˡ-≤
  ; +-monoʳ-<; 1/pos⇒pos; positive⁻¹; ≤-<-trans; +-comm; *-zeroˡ; *-zeroʳ
  ; *-identityˡ; *-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using
  (cancel-add; sub-cancel-common; sub-add-split; sub-shift-cancel; lt-sub
  ; lt-add; lt-shift; le-sub-shift; sub-lt; sub-sub)
open import Real using (ε; CauchySeq; embed; 0<embed; embed-mono-≤; 0<ε)
open import Real.CauchyToInterval using (point; centre-point; M; K; μ≤M)
open import Real.IntervalEquiv using (centre; l; u)
open import Real.Interval using (δ; δ-half; pos-pow)
open import Real.Interval.Arith using (1ℝ)
open import Real.Interval.ContinuityRecipBasic using (l-cauchy→realI; u-cauchy→realI)
open import Real.Interval.Complete using (_⟶_)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Exp.Core as ExpCore using
  (term; term-nonNeg; expPartial; expSeq; expq; expPartial-zero; expPartial-suc
  ; sumQ-mono; div-suc-nonNeg; sucNonZero; sub-nonNeg; _≤ℕ_)
open import Real.Interval.Exp.Approx using (expq-approx)
open import Real.Interval.Embed using (centre-embedℚ)
open import Real.Interval.Kit using (abs-swap; *-mono-≤-nonNeg; recip-antitone)
open import Real.Interval.LimitLaws using
  (abs<⇒lower; abs<⇒upper; add-right-<; ⟶-unique)
open import Real.Interval.Mul.Order using (δ-below)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- L3: monotonicity of expq
--
-- L3：expq 的单调性

-- The partial sums are monotone in the argument. The two Cauchy moduli
-- sample expq q and expq p at different indices, so the comparison cannot
-- be made level by level; instead both samples are pulled to the common
-- index M p j + M q j, where the Cauchy bounds at level K j apply. The
-- resulting discrepancy is of order eps (K j), while a strict gap at
-- level j forces a difference of order 2 delta j, and eps (K j) <= delta j
-- because K j = 2^(j+2) dominates 2^(j+1).
--
-- 部分和对自变量单调。两条柯西模数在各自不同的指数上采样 expq q 与
-- expq p，故无法逐层比较；改为把两个采样点同时拉到共同指数
-- M p j + M q j，在那里适用第 K j 层的柯西界。所得偏差是 eps (K j) 量级，
-- 而第 j 层的严格间隙强迫出 2 delta j 量级的差，又因 K j = 2^(j+2)
-- 支配 2^(j+1)，故 eps (K j) <= delta j，矛盾。
cancel-<-add : (x y z : ℚ) → x + z < y + z → x < y
cancel-<-add x y z h =
  subst₂ (λ a b → a < b) (cancel-add x z) (cancel-add y z)
    (add-right-< {x = x + z} {y = y + z} {z = neg z} h)

-- Division by a fixed positive denominator is monotone in the numerator.
--
-- 固定正分母的商对分子单调。
div-mono : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q≤p : q ≤ p) (k : ℕ)
         → _÷_ q (embed (suc k)) {{sucNonZero k}}
         ≤ _÷_ p (embed (suc k)) {{sucNonZero k}}
div-mono q p 0≤q q≤p k =
  let inv = 1/_ (embed (suc k)) {{sucNonZero k}}
      0≤inv : 0ℚ ≤ inv
      0≤inv = <⇒≤ (positive⁻¹ inv
        {{1/pos⇒pos (embed (suc k)) {{positive (0<embed k)}}}})
  in *-mono-≤-nonNeg {a = q} {a' = p} {b = inv} {b' = inv}
       0≤q q≤p 0≤inv (≤-refl {inv})

-- Terms are monotone in the argument.
--
-- 通项对自变量单调。
term-mono : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q≤p : q ≤ p) (k : ℕ)
          → term q k ≤ term p k
term-mono q p 0≤q q≤p zero = ≤-refl
term-mono q p 0≤q q≤p (suc k) =
  let ih = term-mono q p 0≤q q≤p k
      dq = div-suc-nonNeg q 0≤q k
      dp = div-mono q p 0≤q q≤p k
  in *-mono-≤-nonNeg {a = term q k} {a' = term p k}
       {b = _÷_ q (embed (suc k)) {{sucNonZero k}}}
       {b' = _÷_ p (embed (suc k)) {{sucNonZero k}}}
       (term-nonNeg q 0≤q k) ih dq dp

-- Partial sums are monotone in the argument.
--
-- 部分和对自变量单调。
expPartial-le-param : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q≤p : q ≤ p) (n : ℕ)
              → expPartial q n ≤ expPartial p n
expPartial-le-param q p 0≤q q≤p n =
  sumQ-mono (term q) (term p) (term-mono q p 0≤q q≤p) n

-- expq is monotone in its argument.
--
-- expq 对自变量单调。
expq-mono : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q≤p : q ≤ p)
          → expq q 0≤q ≤ℝ expq p (≤-trans 0≤q q≤p)
expq-mono q p 0≤q q≤p (j , gap) =
  let 0≤p : 0ℚ ≤ p
      0≤p = ≤-trans 0≤q q≤p
      csP = expSeq p 0≤p
      csQ = expSeq q 0≤q
      ap = CauchySeq.f csP (M csP j)
      aq = CauchySeq.f csQ (M csQ j)
      n = M csP j +ℕ M csQ j
      Mp≤n : M csP j ≤ℕ n
      Mp≤n = NatP.m≤m+n (M csP j) (M csQ j)
      Mq≤n : M csQ j ≤ℕ n
      Mq≤n = NatP.m≤n+m (M csQ j) (M csP j)
      anp = CauchySeq.f csP n
      anq = CauchySeq.f csQ n
      hp : ∣ ap - anp ∣ < ε (K j)
      hp = CauchySeq.cauchy csP (K j) (M csP j) n
             (μ≤M csP j) (NatP.≤-trans (μ≤M csP j) Mp≤n)
      hq : ∣ aq - anq ∣ < ε (K j)
      hq = CauchySeq.cauchy csQ (K j) (M csQ j) n
             (μ≤M csQ j) (NatP.≤-trans (μ≤M csQ j) Mq≤n)
      up : anp < ap + ε (K j)
      up = abs<⇒upper {a = ap} {c = anp} {e = ε (K j)}
             (subst (λ z → z < ε (K j)) (abs-swap ap anp) hp)
      hq' : ∣ anq - aq ∣ < ε (K j)
      hq' = subst (λ z → z < ε (K j)) (abs-swap aq anq) hq
      lo : aq - ε (K j) < anq
      lo = abs<⇒lower {a = aq} {c = anq} {e = ε (K j)} hq'
      le : anq ≤ anp
      le = expPartial-le-param q p 0≤q q≤p n
      mid : aq - ε (K j) < anp
      mid = <-≤-trans lo le
      u0 : aq - ε (K j) < ap + ε (K j)
      u0 = <-trans mid up
      u1 : (aq - ε (K j)) + ε (K j) < (ap + ε (K j)) + ε (K j)
      u1 = add-right-< {x = aq - ε (K j)} {y = ap + ε (K j)}
             {z = ε (K j)} u0
      uL : (aq + neg (ε (K j))) + ε (K j) ≡ aq
      uL = trans (+-assoc aq (neg (ε (K j))) (ε (K j)))
             (trans (cong (aq +_) (+-inverseˡ (ε (K j)))) (+-identityʳ aq))
      uR : (ap + ε (K j)) + ε (K j) ≡ ap + (ε (K j) + ε (K j))
      uR = +-assoc ap (ε (K j)) (ε (K j))
      upper : aq < ap + (ε (K j) + ε (K j))
      upper = subst₂ (λ x y → x < y) uL uR u1
      uEqP : u (expq p 0≤p) j ≡ ap + δ j
      uEqP = u-cauchy→realI csP j
      lEqQ : l (expq q 0≤q) j ≡ aq + neg (δ j)
      lEqQ = l-cauchy→realI csQ j
      g0 : ap + δ j < aq + neg (δ j)
      g0 = subst₂ (λ x y → x < y) uEqP lEqQ gap
      gAdd : (ap + δ j) + δ j < (aq + neg (δ j)) + δ j
      gAdd = add-right-< {x = ap + δ j} {y = aq + neg (δ j)} {z = δ j} g0
      gL : (ap + δ j) + δ j ≡ ap + (δ j + δ j)
      gL = +-assoc ap (δ j) (δ j)
      gR : (aq + neg (δ j)) + δ j ≡ aq
      gR = trans (+-assoc aq (neg (δ j)) (δ j))
             (trans (cong (aq +_) (+-inverseˡ (δ j))) (+-identityʳ aq))
      g1 : ap + (δ j + δ j) < aq
      g1 = subst₂ (λ x y → x < y) gL gR gAdd
      sameL : ap + (δ j + δ j) < ap + (ε (K j) + ε (K j))
      sameL = <-trans g1 upper
      cmL : ap + (δ j + δ j) ≡ (δ j + δ j) + ap
      cmL = +-comm ap (δ j + δ j)
      cmR : ap + (ε (K j) + ε (K j)) ≡ (ε (K j) + ε (K j)) + ap
      cmR = +-comm ap (ε (K j) + ε (K j))
      sw : (δ j + δ j) + ap < (ε (K j) + ε (K j)) + ap
      sw = subst₂ (λ x y → x < y) cmL cmR sameL
      δδ<εε : δ j + δ j < ε (K j) + ε (K j)
      δδ<εε = cancel-<-add (δ j + δ j) (ε (K j) + ε (K j)) ap sw
      zpos : 0ℚ < embed (2 ^ suc j)
      zpos = positive⁻¹ (embed (2 ^ suc j)) {{pos-pow j}}
      pow≤ : 2 ^ suc j ≤ℕ suc (K j)
      pow≤ = NatP.≤-trans (NatP.m≤n*m (2 ^ suc j) 2) (NatP.n≤1+n (K j))
      emb≤ : embed (2 ^ suc j) ≤ embed (suc (K j))
      emb≤ = embed-mono-≤ pow≤
      εK≤δ : ε (K j) ≤ δ j
      εK≤δ = recip-antitone {a = embed (2 ^ suc j)} {b = embed (suc (K j))}
               zpos emb≤
      εε≤δδ : ε (K j) + ε (K j) ≤ δ j + δ j
      εε≤δδ = +-mono-≤ εK≤δ εK≤δ
      selfLt : ε (K j) + ε (K j) < ε (K j) + ε (K j)
      selfLt = ≤-<-trans εε≤δδ δδ<εε
  in ⊥-elim (<-asym selfLt selfLt)

------------------------------------------------------------------------
-- L5: exp 0 = 1
--
-- L5：exp 0 = 1

-- At q = 0 the zeroth term is 1 and every later term is 0, so the partial
-- sums are constantly 1 from index 1 on. The sequence of points therefore
-- converges to 1ℝ, and uniqueness of limits turns that into equality with
-- expq 0 0<=0.
--
-- q = 0 时第零项为 1、其后每项为 0，故从下标 1 起部分和恒等于 1。于是点序列
-- 收敛到 1ℝ，再由极限唯一性得到与 expq 0 0≤0 的相等。
term-zero-0 : term 0ℚ zero ≡ 1ℚ
term-zero-0 = refl

term-zero-suc : (k : ℕ) → term 0ℚ (suc k) ≡ 0ℚ
term-zero-suc k =
  trans (cong (λ z → term 0ℚ k * z) (*-zeroˡ (1/_ (embed (suc k)) {{sucNonZero k}})))
        (*-zeroʳ (term 0ℚ k))

expPartial-one : (m : ℕ) → expPartial 0ℚ (suc m) ≡ 1ℚ
expPartial-one zero =
  trans (expPartial-suc 0ℚ zero)
    (trans (cong₂ _+_ (expPartial-zero 0ℚ) term-zero-0)
           (+-identityˡ 1ℚ))
expPartial-one (suc m) =
  trans (expPartial-suc 0ℚ (suc m))
    (trans (cong₂ _+_ (expPartial-one m) (term-zero-suc m))
           (+-identityʳ 1ℚ))

expPartial-one-le : (n : ℕ) → 1 ≤ℕ n → expPartial 0ℚ n ≡ 1ℚ
expPartial-one-le zero ()
expPartial-one-le (suc m) _ = expPartial-one m

expq-zero-point : (λ n → point (expPartial 0ℚ n)) ⟶ 1ℝ
expq-zero-point k =
  let N = suc zero
      h : ∀ n → N ≤ℕ n → ∣ centre (point (expPartial 0ℚ n)) k - centre 1ℝ k ∣ < ε k
      h = λ n n≥ →
        let e1 : centre (point (expPartial 0ℚ n)) k ≡ expPartial 0ℚ n
            e1 = centre-point (expPartial 0ℚ n) k
            e2 : centre 1ℝ k ≡ 1ℚ
            e2 = centre-embedℚ 1ℚ k
            e3 : expPartial 0ℚ n ≡ 1ℚ
            e3 = expPartial-one-le n n≥
            z : centre (point (expPartial 0ℚ n)) k - centre 1ℝ k ≡ 0ℚ
            z = trans (cong₂ (λ a b → a - b) e1 e2)
                  (trans (cong (λ a → a - 1ℚ) e3) (+-inverseʳ 1ℚ))
        in subst (λ v → ∣ v ∣ < ε k) (sym z) (0<ε k)
  in N , h

expq-zero : expq 0ℚ (≤-refl {0ℚ}) ≈ℝ 1ℝ
expq-zero = ⟶-unique (expq-approx 0ℚ (≤-refl {0ℚ})) expq-zero-point

------------------------------------------------------------------------
-- L6: strict monotonicity of expq
--
-- L6：expq 的严格单调性

term-one : (q : ℚ) → term q (suc zero) ≡ q
term-one q =
  begin
    term q (suc zero)
      ≡⟨ refl ⟩
    1ℚ * (q * 1/_ (embed (suc zero)))
      ≡⟨ cong (λ z → 1ℚ * (q * z)) embed-inv ⟩
    1ℚ * (q * 1ℚ)
      ≡⟨ *-identityˡ (q * 1ℚ) ⟩
    q * 1ℚ
      ≡⟨ *-identityʳ q ⟩
    q
  ∎
  where
    embed-inv : 1/_ (embed (suc zero)) ≡ 1ℚ
    embed-inv = refl

-- The second partial sum is 1 + q.
--
-- 第二个部分和等于 1 + q。
expPartial-two : (q : ℚ) → expPartial q (suc (suc zero)) ≡ 1ℚ + q
expPartial-two q =
  begin
    expPartial q (suc (suc zero))
      ≡⟨ expPartial-suc q (suc zero) ⟩
    expPartial q (suc zero) + term q (suc zero)
      ≡⟨ cong₂ _+_ one (term-one q) ⟩
    1ℚ + q
  ∎
  where
    one : expPartial q (suc zero) ≡ 1ℚ
    one = trans (expPartial-suc q zero) (+-identityˡ 1ℚ)

-- The difference p - q survives in the partial sums.
-- From index two on, every step adds term p k - term q k >= 0, so the
-- first step p - q is never lost. Induction on m, with the base case
-- collapsing by expPartial-two.
--
-- 差值 p - q 在部分和中保留。
-- 从下标 2 起每一步都加上 term p k - term q k >= 0，故首个 p - q 不会被
-- 冲掉。对 m 归纳，基例由 expPartial-two 化简。
diff-lower : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q≤p : q ≤ p) (m : ℕ)
  → p - q ≤ expPartial p (suc (suc m)) - expPartial q (suc (suc m))
diff-lower q p 0≤q q≤p zero =
  let A = expPartial-two p
      B = expPartial-two q
      t : p - q ≤ (1ℚ + p) - (1ℚ + q)
      t = subst (λ z → p - q ≤ z) (sym (sub-cancel-common 1ℚ p q)) (≤-refl {p - q})
  in subst₂ (λ x y → p - q ≤ x - y) (sym A) (sym B) t
diff-lower q p 0≤q q≤p (suc m) =
  let A0 = expPartial p (suc (suc m))
      B0 = expPartial q (suc (suc m))
      u  = term p (suc (suc m))
      v  = term q (suc (suc m))
      ih = diff-lower q p 0≤q q≤p m
      nn : 0ℚ ≤ u - v
      nn = sub-nonNeg v u (term-mono q p 0≤q q≤p (suc (suc m)))
      mono = +-mono-≤ ih nn
      m1 : p - q ≤ (A0 - B0) + (u - v)
      m1 = subst (λ z → z ≤ (A0 - B0) + (u - v)) (+-identityʳ (p - q)) mono
  in subst (λ z → p - q ≤ z) (sym (sub-add-split A0 B0 u v)) m1

expq-strict-mono : (q p : ℚ) (0≤q : 0ℚ ≤ q) (q<p : q < p)
                 → expq q 0≤q <ℝ expq p (≤-trans 0≤q (<⇒≤ q<p))
expq-strict-mono q p 0≤q q<p =
  let 0≤p : 0ℚ ≤ p
      0≤p = ≤-trans 0≤q (<⇒≤ q<p)
      pq>0 : 0ℚ < p - q
      pq>0 = subst (λ z → z < p + neg q) (+-inverseʳ q) (+-monoˡ-< (neg q) q<p)
      m , _ , δm<pq = δ-below (p - q) pq>0 0
      j = suc (suc m)
      csP = expSeq p 0≤p
      csQ = expSeq q 0≤q
      ap = CauchySeq.f csP (M csP j)
      aq = CauchySeq.f csQ (M csQ j)
      k = M csP j +ℕ M csQ j
      n = suc (suc k)
      n≥Mp : M csP j ≤ℕ n
      n≥Mp = NatP.≤-trans (NatP.m≤m+n (M csP j) (M csQ j))
               (NatP.≤-trans (NatP.n≤1+n k) (NatP.n≤1+n (suc k)))
      n≥Mq : M csQ j ≤ℕ n
      n≥Mq = NatP.≤-trans (NatP.m≤n+m (M csQ j) (M csP j))
               (NatP.≤-trans (NatP.n≤1+n k) (NatP.n≤1+n (suc k)))
      anp = CauchySeq.f csP n
      anq = CauchySeq.f csQ n
      hP : ∣ ap - anp ∣ < ε (K j)
      hP = CauchySeq.cauchy csP (K j) (M csP j) n (μ≤M csP j)
             (NatP.≤-trans (μ≤M csP j) n≥Mp)
      hQ : ∣ aq - anq ∣ < ε (K j)
      hQ = CauchySeq.cauchy csQ (K j) (M csQ j) n (μ≤M csQ j)
             (NatP.≤-trans (μ≤M csQ j) n≥Mq)
      upP : anp < ap + ε (K j)
      upP = abs<⇒upper {a = ap} {c = anp} {e = ε (K j)}
              (subst (λ z → z < ε (K j)) (abs-swap ap anp) hP)
      loP : anp - ε (K j) < ap
      loP = lt-sub anp ap (ε (K j)) upP
      hQ' : ∣ anq - aq ∣ < ε (K j)
      hQ' = subst (λ z → z < ε (K j)) (abs-swap aq anq) hQ
      loQ : aq - ε (K j) < anq
      loQ = abs<⇒lower {a = aq} {c = anq} {e = ε (K j)} hQ'
      upQ : aq < anq + ε (K j)
      upQ = lt-add aq anq (ε (K j)) loQ
      B : p - q ≤ anp - anq
      B = diff-lower q p 0≤q (<⇒≤ q<p) k
      zpos : 0ℚ < embed (2 ^ suc j)
      zpos = positive⁻¹ (embed (2 ^ suc j)) {{pos-pow j}}
      pow≤ : 2 ^ suc j ≤ℕ suc (K j)
      pow≤ = NatP.≤-trans (NatP.m≤n*m (2 ^ suc j) 2) (NatP.n≤1+n (K j))
      emb≤ : embed (2 ^ suc j) ≤ embed (suc (K j))
      emb≤ = embed-mono-≤ pow≤
      εK≤δ : ε (K j) ≤ δ j
      εK≤δ = recip-antitone {a = embed (2 ^ suc j)} {b = embed (suc (K j))}
               zpos emb≤
      εε≤δδ : ε (K j) + ε (K j) ≤ δ j + δ j
      εε≤δδ = +-mono-≤ εK≤δ εK≤δ
      fourδ : (δ j + δ j) + (δ j + δ j) ≡ δ m
      fourδ = trans (cong₂ _+_ (δ-half (suc m)) (δ-half (suc m))) (δ-half m)
      S≤δm : (ε (K j) + ε (K j)) + (δ j + δ j) ≤ δ m
      S≤δm = subst (λ z → (ε (K j) + ε (K j)) + (δ j + δ j) ≤ z) fourδ
               (+-mono-≤ εε≤δδ (≤-refl {δ j + δ j}))
      S<pq : (ε (K j) + ε (K j)) + (δ j + δ j) < p - q
      S<pq = ≤-<-trans S≤δm δm<pq
      δδ≤pqsub : δ j + δ j ≤ (p - q) - (ε (K j) + ε (K j))
      δδ≤pqsub = le-sub-shift (p - q) (ε (K j) + ε (K j)) (δ j + δ j) (<⇒≤ S<pq)
      subMono : (p - q) - (ε (K j) + ε (K j))
                ≤ (anp - anq) - (ε (K j) + ε (K j))
      subMono = +-monoˡ-≤ (neg (ε (K j) + ε (K j))) B
      subSub : (anp - ε (K j)) - (anq + ε (K j))
               ≡ (anp - anq) - (ε (K j) + ε (K j))
      subSub = sub-sub anp anq (ε (K j)) (ε (K j))
      s1 : (anp - ε (K j)) - (anq + ε (K j)) < ap - aq
      s1 = sub-lt (anp - ε (K j)) ap aq (anq + ε (K j)) loP upQ
      s2 : (anp - anq) - (ε (K j) + ε (K j)) < ap - aq
      s2 = subst (λ z → z < ap - aq) subSub s1
      twoδ<apq : δ j + δ j < ap - aq
      twoδ<apq = ≤-<-trans (≤-trans δδ≤pqsub subMono) s2
      addq : aq + (δ j + δ j) < aq + (ap - aq)
      addq = +-monoʳ-< aq twoδ<apq
      cancelq : aq + (ap - aq) ≡ ap
      cancelq = trans (+-comm aq (ap - aq)) (sub-shift-cancel ap aq)
      h2 : aq + (δ j + δ j) < ap
      h2 = subst (λ z → aq + (δ j + δ j) < z) cancelq addq
      assocL : (aq + δ j) + δ j ≡ aq + (δ j + δ j)
      assocL = +-assoc aq (δ j) (δ j)
      h3 : (aq + δ j) + δ j < ap
      h3 = subst (λ z → z < ap) (sym assocL) h2
      h4 : aq + δ j < ap - δ j
      h4 = lt-shift (aq + δ j) ap (δ j) h3
      uEqQ : u (expq q 0≤q) j ≡ aq + δ j
      uEqQ = u-cauchy→realI csQ j
      lEqP : l (expq p 0≤p) j ≡ ap + neg (δ j)
      lEqP = l-cauchy→realI csP j
  in j , subst₂ (λ x y → x < y) (sym uEqQ) (sym lEqP) h4

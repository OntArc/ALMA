------------------------------------------------------------------------
-- Partial sums stay below the Cauchy limit
--
-- 部分和不超过柯西极限
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.PartialLe where

open import Data.Empty using (⊥-elim)
open import Data.Nat as Nat using (ℕ; zero; suc; _^_)
  renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
import Data.Nat.Properties as NatP
open import Data.Product using (_,_; proj₁)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _≤_; _<_; _+_; _-_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; <-≤-trans; <-trans; <-asym; +-mono-≤
  ; +-identityˡ; +-identityʳ; +-inverseˡ; +-assoc; +-comm; ≤-<-trans; positive⁻¹)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; subst; subst₂)

open import Real using (ε; CauchySeq; embed; embed-mono-≤)
open import Real.CauchyToInterval using (M; K; μ≤M)
open import Real.Interval using (RealI; δ; δ-pos; pos-pow; embedℚ)
open import Real.IntervalEquiv using (l; u)
open import Real.Interval.ContinuityRecipBasic using
  (l-cauchy→realI; u-cauchy→realI)
open import Real.Interval.Exp.Order using (cancel-<-add)
open import Real.Interval.Exp.Core using
  (expPartial; expSeq; expq; expPartial-le; expPartial-cauchy)
open import Real.Interval.Kit using (abs-swap; recip-antitone)
open import Real.Interval.LimitLaws using (abs<⇒upper; add-right-<)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)

------------------------------------------------------------------------
-- The sampled precision is below the layer radius
--
-- 采样精度低于该层半径

εK≤δ : (j : ℕ) → ε (K j) ≤ δ j
εK≤δ j =
  let zpos : 0ℚ < embed (2 ^ suc j)
      zpos = positive⁻¹ (embed (2 ^ suc j)) {{pos-pow j}}

      pow≤ : 2 ^ suc j ≤ℕ suc (K j)
      pow≤ = NatP.≤-trans (NatP.m≤n*m (2 ^ suc j) 2)
              (NatP.n≤1+n (K j))

      emb≤ : embed (2 ^ suc j) ≤ embed (suc (K j))
      emb≤ = embed-mono-≤ pow≤
  in
    recip-antitone {a = embed (2 ^ suc j)} {b = embed (suc (K j))}
      zpos emb≤

------------------------------------------------------------------------
-- The main bound
--
-- 主界

expPartial-le-expq : (q : ℚ) (0≤q : 0ℚ ≤ q) (n : ℕ)
                   → embedℚ (expPartial q n) ≤ℝ expq q 0≤q
expPartial-le-expq q 0≤q n (j , gap) =
  let
    cs : CauchySeq
    cs = expSeq q 0≤q

    dj : ℚ
    dj = δ j

    ap : ℚ
    ap = expPartial q (M cs j)

    a₀ : ℚ
    a₀ = expPartial q n

    eU : u (expq q 0≤q) j ≡ ap + dj
    eU = u-cauchy→realI cs j

    eL : l (embedℚ a₀) j ≡ neg dj + a₀
    eL = l-dyadic a₀ j

    g0 : ap + dj < neg dj + a₀
    g0 = subst₂ (λ x y → x < y) eU eL gap

    gAdd : (ap + dj) + dj < (neg dj + a₀) + dj
    gAdd = add-right-< {x = ap + dj} {y = neg dj + a₀} {z = dj} g0

    gL : (ap + dj) + dj ≡ ap + (dj + dj)
    gL = +-assoc ap dj dj

    gR : (neg dj + a₀) + dj ≡ a₀
    gR = trans (+-assoc (neg dj) a₀ dj)
           (trans (cong (λ z → neg dj + z) (+-comm a₀ dj))
             (trans (sym (+-assoc (neg dj) dj a₀))
               (trans (cong (λ z → z + a₀) (+-inverseˡ dj))
                 (+-identityˡ a₀))))

    g1 : ap + (dj + dj) < a₀
    g1 = subst₂ (λ x y → x < y) gL gR gAdd

    μK : ℕ
    μK = proj₁ (expPartial-cauchy q 0≤q (K j))

    N : ℕ
    N = (μK +ℕ M cs j) +ℕ n

    μ≤Mj : μK ≤ℕ M cs j
    μ≤Mj = μ≤M cs j

    μ≤N₁ : μK ≤ℕ μK +ℕ M cs j
    μ≤N₁ = NatP.m≤m+n μK (M cs j)

    N₁≤N : μK +ℕ M cs j ≤ℕ N
    N₁≤N = NatP.m≤m+n (μK +ℕ M cs j) n

    μ≤N : μK ≤ℕ N
    μ≤N = NatP.≤-trans μ≤N₁ N₁≤N

    n≤N : n ≤ℕ N
    n≤N = NatP.m≤n+m n (μK +ℕ M cs j)

    aN : ℚ
    aN = expPartial q N

    hp : ∣ ap - aN ∣ < ε (K j)
    hp = CauchySeq.cauchy cs (K j) (M cs j) N μ≤Mj μ≤N

    up : aN < ap + ε (K j)
    up = abs<⇒upper {a = ap} {c = aN} {e = ε (K j)}
           (subst (λ z → z < ε (K j)) (abs-swap ap aN) hp)

    le₀ : a₀ ≤ aN
    le₀ = expPartial-le q 0≤q n N n≤N

    mid : ap + (dj + dj) < aN
    mid = <-≤-trans g1 le₀

    upper : ap + (dj + dj) < ap + ε (K j)
    upper = <-trans mid up

    cmL : ap + (dj + dj) ≡ (dj + dj) + ap
    cmL = +-comm ap (dj + dj)

    cmR : ap + ε (K j) ≡ ε (K j) + ap
    cmR = +-comm ap (ε (K j))

    sw : (dj + dj) + ap < ε (K j) + ap
    sw = subst₂ (λ x y → x < y) cmL cmR upper

    δδ<ε : dj + dj < ε (K j)
    δδ<ε = cancel-<-add (dj + dj) (ε (K j)) ap sw

    δ≤δδ : dj ≤ dj + dj
    δ≤δδ = ≤-trans (≤-reflexive (sym (+-identityʳ dj)))
             (+-mono-≤ (≤-refl {dj}) (<⇒≤ (δ-pos j)))

    ε≤δδ : ε (K j) ≤ dj + dj
    ε≤δδ = ≤-trans (εK≤δ j) δ≤δδ

    selfLt : ε (K j) < ε (K j)
    selfLt = ≤-<-trans ε≤δδ δδ<ε
  in
    ⊥-elim (<-asym selfLt selfLt)

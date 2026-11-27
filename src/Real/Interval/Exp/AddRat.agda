------------------------------------------------------------------------
-- The exponential addition law at rational points
--
-- 有理点处的指数加法律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Exp.AddRat where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
  renaming (≤-trans to ≤ℕ-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_)
open import Data.Rational.Base using (nonNegative)
open import Data.Rational.Properties using
  (≤-trans; ≤-refl; ≤-reflexive; ≤-<-trans; <⇒≤; +-mono-≤; +-assoc; *-comm
  ; *-identityˡ; *-identityʳ; *-distribˡ-+; *-distribʳ-+; *-monoˡ-≤-nonNeg)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂)

open import Base.RationalRing using (0<1)
open import Real using (half; ε; 0<ε)
open import Real.Archimedean using (rat-shrink; ε-≤-1; le-add-right)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-comm; +ℝ-assoc; +ℝ-identityʳ; sub-add-cancelℝ)
open import Real.Interval.Continuity using (embedℚ-mono)
open import Real.Interval.DensityArch using (≤ℝ-of-slack)
open import Real.Interval.Embed using (embedℚ-+; embedℚ-*; embedℚ-cong)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Elementary.Exp using (expℝ; expℝ-le-of-partials)
open import Real.Interval.Elementary.ExpLaws using
  (expPartialℝ-le-expℝ; expPartialℝ-approx; expℝ-nonNeg)
open import Real.Interval.Elementary.ExpRat using
  (embed-nonNeg; expPartialℝ-at-rat)
open import Real.Interval.Exp.Series using
  (expPartialℝ; expPartialℝ-nonNeg; expPartialℝ-index-mono)
open import Real.Interval.Exp.Core using (expPartial; expPartial-nonNeg)
open import Real.Interval.Exp.Lipschitz using (expPartial-bound)
open import Real.Interval.Exp.ProductReal using (expPartial-add-close-rat)
open import Real.Interval.Kit using (two-half)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Order using (*ℝ-≤-mono; +ℝ-cong)
open import Real.Interval.Mul.Laws using
  (*ℝ-comm; *ℝ-assoc; *ℝ-distribˡ-+; *ℝ-distribʳ-+)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_; ≤ℝ-trans)
open import Real.Interval.OrderLe using
  (<⇒≤ℝ; ≤ℝ-refl; ≤ℝ-antisym; ≤ℝ-+-mono; ≤ℝ-+-monoˡ; ≤ℝ-resp-≈
  ; <-≤ℝ-trans; ≈⇒≤ℝ)
open import Real.Interval.OrderLaws using
  (halved-tolerance-pos; halved-tolerance-below; ≈-<-resp; <-+mono)
open import Real.Interval.Sqrt.Bounds using (embedℚ-≤)

------------------------------------------------------------------------
-- The doubled point stays below the product of the two cuts
--
-- 倍长点处的割不高于两割之积

-- The cut at the doubled point is dominated by the product, where both
-- points are non-negative rationals.
--
-- 当两个点都是非负有理数时，倍长点处的割被两割之积支配。
expℝ-add-rat-le : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q)
                → expℝ (embedℚ (p + q)) (embed-nonNeg (p + q) (≤-trans 0≤p (le-add-right p q 0≤q)))
                  ≤ℝ expℝ (embedℚ p) (embed-nonNeg p 0≤p)
                     *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expℝ-add-rat-le p q 0≤p 0≤q =
  let
    ep : RealI
    ep = embedℚ p

    eq : RealI
    eq = embedℚ q

    epq : RealI
    epq = embedℚ (p + q)

    0≤ep : 0ℝ ≤ℝ ep
    0≤ep = embed-nonNeg p 0≤p

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)

    0≤epq : 0ℝ ≤ℝ epq
    0≤epq = embed-nonNeg (p + q) 0≤pq

    A : RealI
    A = expℝ ep 0≤ep

    B : RealI
    B = expℝ eq 0≤eq

    L : RealI
    L = A *ℝ B

    0≤A : 0ℝ ≤ℝ A
    0≤A = expℝ-nonNeg ep 0≤ep

    C : RealI
    C = expℝ epq 0≤epq

    hyp : (e : ℚ) → 0ℚ < e → C ≤ℝ L +ℝ embedℚ e
    hyp e 0<e =
      let
        d : ℚ
        d = e * half

        0<d : 0ℚ < d
        0<d = halved-tolerance-pos e 0<e

        d<e : d < e
        d<e = halved-tolerance-below e 0<e

        d≤e : embedℚ d ≤ℝ embedℚ e
        d≤e = <⇒≤ℝ (embedℚ-mono d e d<e)

        cl : Σ ℕ (λ N → ∀ n → N ≤ℕ n
               → (expPartialℝ ep n *ℝ expPartialℝ eq n
                    -ℝ embedℚ d
                  <ℝ expPartialℝ epq (n +ℕ n))
                 × (expPartialℝ epq (n +ℕ n)
                  <ℝ expPartialℝ ep n *ℝ expPartialℝ eq n +ℝ embedℚ d))
        cl = expPartial-add-close-rat p q 0≤p 0≤q d 0<d

        N₀ : ℕ
        N₀ = proj₁ cl

        close : ∀ n → N₀ ≤ℕ n
              → (expPartialℝ ep n *ℝ expPartialℝ eq n -ℝ embedℚ d
                <ℝ expPartialℝ epq (n +ℕ n))
               × (expPartialℝ epq (n +ℕ n)
                <ℝ expPartialℝ ep n *ℝ expPartialℝ eq n +ℝ embedℚ d)
        close = proj₂ cl
      in
        expℝ-le-of-partials epq 0≤epq (L +ℝ embedℚ e) (λ k →
          let
            n : ℕ
            n = k +ℕ N₀

            nn : ℕ
            nn = n +ℕ n

            le₁ : expPartialℝ epq k ≤ℝ expPartialℝ epq n
            le₁ = expPartialℝ-index-mono epq 0≤epq k n (m≤m+n k N₀)

            le₂ : expPartialℝ epq n ≤ℝ expPartialℝ epq nn
            le₂ = expPartialℝ-index-mono epq 0≤epq n nn (m≤m+n n n)

            N₀≤n : N₀ ≤ℕ n
            N₀≤n = m≤n+m N₀ k

            ub : expPartialℝ epq nn
               <ℝ expPartialℝ ep n *ℝ expPartialℝ eq n +ℝ embedℚ d
            ub = proj₂ (close n N₀≤n)

            P : RealI
            P = expPartialℝ ep n

            Q : RealI
            Q = expPartialℝ eq n

            P≤A : P ≤ℝ A
            P≤A = expPartialℝ-le-expℝ ep 0≤ep n

            Q≤B : Q ≤ℝ B
            Q≤B = expPartialℝ-le-expℝ eq 0≤eq n

            0≤Q : 0ℝ ≤ℝ Q
            0≤Q = expPartialℝ-nonNeg eq 0≤eq n

            prod≤ : P *ℝ Q ≤ℝ L
            prod≤ = ≤ℝ-trans
                      (*ℝ-≤-mono P A Q P≤A 0≤Q)
                      (≤ℝ-resp-≈ (*ℝ-comm Q A) (*ℝ-comm B A)
                                 (*ℝ-≤-mono Q B A Q≤B 0≤A))

            shift : L +ℝ embedℚ d ≤ℝ L +ℝ embedℚ e
            shift = ≤ℝ-resp-≈ (≈ℝ-sym (+ℝ-comm L (embedℚ d)))
                               (≈ℝ-sym (+ℝ-comm L (embedℚ e)))
                               (≤ℝ-+-mono {x = embedℚ d} {y = embedℚ e} {z = L} d≤e)

            final : expPartialℝ epq k ≤ℝ L +ℝ embedℚ e
            final = ≤ℝ-trans (≤ℝ-trans le₁ le₂)
                      (≤ℝ-trans (<⇒≤ℝ ub)
                        (≤ℝ-trans (≤ℝ-+-mono {z = embedℚ d} prod≤)
                          shift))
          in final)
  in
    ≤ℝ-of-slack C L hyp

------------------------------------------------------------------------
-- The product of the two cuts stays below the doubled point
--
-- 两割之积不高于倍长点处的割

-- The product is dominated by the cut at the doubled point, where both
-- points are non-negative rationals. The budget splits the tolerance in
-- halves: one half pays for the rational closeness of the product to the
-- doubled partial sum, the other for the four-term expansion of the
-- widened product.
--
-- 当两个点都是非负有理数时，两割之积被倍长点处的割支配。预算把容差一分为二：
-- 一半支付乘积与倍长部分和的有理接近性，另一半支付展宽后乘积的四项展开。
expℝ-add-rat-ge : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q)
                → expℝ (embedℚ p) (embed-nonNeg p 0≤p)
                   *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
                  ≤ℝ expℝ (embedℚ (p + q)) (embed-nonNeg (p + q) (≤-trans 0≤p (le-add-right p q 0≤q)))
expℝ-add-rat-ge p q 0≤p 0≤q =
  let
    ep : RealI
    ep = embedℚ p

    eq : RealI
    eq = embedℚ q

    epq : RealI
    epq = embedℚ (p + q)

    0≤ep : 0ℝ ≤ℝ ep
    0≤ep = embed-nonNeg p 0≤p

    0≤eq : 0ℝ ≤ℝ eq
    0≤eq = embed-nonNeg q 0≤q

    0≤pq : 0ℚ ≤ p + q
    0≤pq = ≤-trans 0≤p (le-add-right p q 0≤q)

    0≤epq : 0ℝ ≤ℝ epq
    0≤epq = embed-nonNeg (p + q) 0≤pq

    A : RealI
    A = expℝ ep 0≤ep

    B : RealI
    B = expℝ eq 0≤eq

    L : RealI
    L = A *ℝ B

    0≤B : 0ℝ ≤ℝ B
    0≤B = expℝ-nonNeg eq 0≤eq

    C : RealI
    C = expℝ epq 0≤epq

    hyp : (e : ℚ) → 0ℚ < e → L ≤ℝ C +ℝ embedℚ e
    hyp e 0<e =
      let
        d : ℚ
        d = e * half

        0<d : 0ℚ < d
        0<d = halved-tolerance-pos e 0<e

        cl : Σ ℕ (λ N → ∀ n → N ≤ℕ n
               → (expPartialℝ ep n *ℝ expPartialℝ eq n
                    -ℝ embedℚ d
                  <ℝ expPartialℝ epq (n +ℕ n))
                 × (expPartialℝ epq (n +ℕ n)
                  <ℝ expPartialℝ ep n *ℝ expPartialℝ eq n +ℝ embedℚ d))
        cl = expPartial-add-close-rat p q 0≤p 0≤q d 0<d

        N₀ : ℕ
        N₀ = proj₁ cl

        close : ∀ n → N₀ ≤ℕ n
              → (expPartialℝ ep n *ℝ expPartialℝ eq n -ℝ embedℚ d
                <ℝ expPartialℝ epq (n +ℕ n))
               × (expPartialℝ epq (n +ℕ n)
                <ℝ expPartialℝ ep n *ℝ expPartialℝ eq n +ℝ embedℚ d)
        close = proj₂ cl

        bp : Σ ℚ (λ K → (n : ℕ) → expPartial p n ≤ K)
        bp = expPartial-bound p 0≤p d 0<d

        Kp : ℚ
        Kp = proj₁ bp

        bndp : (n : ℕ) → expPartialℝ ep n ≤ℝ embedℚ Kp
        bndp n = ≤ℝ-trans (≈⇒≤ℝ (expPartialℝ-at-rat p 0≤p n))
                   (embedℚ-≤ (expPartial p n) Kp (proj₂ bp n))

        0≤Kp : 0ℚ ≤ Kp
        0≤Kp = ≤-trans (expPartial-nonNeg p 0≤p 0) (proj₂ bp 0)

        bq : Σ ℚ (λ K → (n : ℕ) → expPartial q n ≤ K)
        bq = expPartial-bound q 0≤q d 0<d

        Kq : ℚ
        Kq = proj₁ bq

        bndq : (n : ℕ) → expPartialℝ eq n ≤ℝ embedℚ Kq
        bndq n = ≤ℝ-trans (≈⇒≤ℝ (expPartialℝ-at-rat q 0≤q n))
                   (embedℚ-≤ (expPartial q n) Kq (proj₂ bq n))

        0≤Kq : 0ℚ ≤ Kq
        0≤Kq = ≤-trans (expPartial-nonNeg q 0≤q 0) (proj₂ bq 0)

        c : ℚ
        c = (Kp + Kq) + 1ℚ

        0≤c : 0ℚ ≤ c
        0≤c = ≤-trans (+-mono-≤ 0≤Kp 0≤Kq)
                (le-add-right (Kp + Kq) 1ℚ (<⇒≤ 0<1))

        sh : Σ ℕ (λ j → ε j * c < d)
        sh = rat-shrink c 0≤c d 0<d

        j : ℕ
        j = proj₁ sh

        shr : ε j * c < d
        shr = proj₂ sh

        e₁ : ℚ
        e₁ = ε j

        0<e₁ : 0ℚ < e₁
        0<e₁ = 0<ε j

        0≤e₁ : 0ℚ ≤ e₁
        0≤e₁ = <⇒≤ 0<e₁

        e₁≤1 : e₁ ≤ 1ℚ
        e₁≤1 = ε-≤-1 j

        E₁ : RealI
        E₁ = embedℚ e₁

        0≤E₁ : 0ℝ ≤ℝ E₁
        0≤E₁ = embed-nonNeg e₁ 0≤e₁

        appp : Σ ℕ (λ N → A ≤ℝ expPartialℝ ep N +ℝ E₁)
        appp = expPartialℝ-approx ep 0≤ep e₁ 0<e₁

        Np : ℕ
        Np = proj₁ appp

        ap : A ≤ℝ expPartialℝ ep Np +ℝ E₁
        ap = proj₂ appp

        appq : Σ ℕ (λ N → B ≤ℝ expPartialℝ eq N +ℝ E₁)
        appq = expPartialℝ-approx eq 0≤eq e₁ 0<e₁

        Nq : ℕ
        Nq = proj₁ appq

        aq : B ≤ℝ expPartialℝ eq Nq +ℝ E₁
        aq = proj₂ appq

        mk : (a b c : ℕ)
           → Σ ℕ (λ n → (a ≤ℕ n) × (b ≤ℕ n) × (c ≤ℕ n))
        mk = λ a b c →
          ((a +ℕ b) +ℕ c)
          , ( ≤ℕ-trans (m≤m+n a b) (m≤m+n (a +ℕ b) c)
            , ( ≤ℕ-trans (m≤n+m b a) (m≤m+n (a +ℕ b) c)
              , m≤n+m c (a +ℕ b) ) )

        idx : Σ ℕ (λ n → (N₀ ≤ℕ n) × (Np ≤ℕ n) × (Nq ≤ℕ n))
        idx = mk N₀ Np Nq

        step
          : (n : ℕ) → N₀ ≤ℕ n → Np ≤ℕ n → Nq ≤ℕ n
          → L ≤ℝ C +ℝ embedℚ e
        step = λ n N₀≤n Np≤n Nq≤n →
          let
            nn : ℕ
            nn = n +ℕ n

            P : RealI
            P = expPartialℝ ep n

            Q : RealI
            Q = expPartialℝ eq n

            R : RealI
            R = expPartialℝ epq nn

            P₀≤P : expPartialℝ ep Np ≤ℝ P
            P₀≤P = expPartialℝ-index-mono ep 0≤ep Np n Np≤n

            Q₀≤Q : expPartialℝ eq Nq ≤ℝ Q
            Q₀≤Q = expPartialℝ-index-mono eq 0≤eq Nq n Nq≤n

            A≤P : A ≤ℝ P +ℝ E₁
            A≤P = ≤ℝ-trans ap (≤ℝ-+-mono {z = E₁} P₀≤P)

            B≤Q : B ≤ℝ Q +ℝ E₁
            B≤Q = ≤ℝ-trans aq (≤ℝ-+-mono {z = E₁} Q₀≤Q)

            0≤P : 0ℝ ≤ℝ P
            0≤P = expPartialℝ-nonNeg ep 0≤ep n

            0≤P+E₁ : 0ℝ ≤ℝ P +ℝ E₁
            0≤P+E₁ = ≤ℝ-trans 0≤P
                       (≤ℝ-resp-≈ (+ℝ-identityʳ P) (≈ℝ-refl)
                         (≤ℝ-+-monoˡ {x = 0ℝ} {y = E₁} {z = P} 0≤E₁))

            AB≤ : L ≤ℝ (P +ℝ E₁) *ℝ (Q +ℝ E₁)
            AB≤ = ≤ℝ-trans
                    (*ℝ-≤-mono A (P +ℝ E₁) B A≤P 0≤B)
                    (≤ℝ-resp-≈ (*ℝ-comm B (P +ℝ E₁))
                               (*ℝ-comm (Q +ℝ E₁) (P +ℝ E₁))
                               (*ℝ-≤-mono B (Q +ℝ E₁) (P +ℝ E₁) B≤Q 0≤P+E₁))

            expand : (P +ℝ E₁) *ℝ (Q +ℝ E₁)
                   ≈ℝ (P *ℝ Q +ℝ P *ℝ E₁) +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁)
            expand = ≈ℝ-trans
                       (*ℝ-distribʳ-+ (Q +ℝ E₁) P E₁)
                       (+ℝ-cong (*ℝ-distribˡ-+ P Q E₁) (*ℝ-distribˡ-+ E₁ Q E₁))

            assocR : (P *ℝ Q +ℝ P *ℝ E₁) +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁)
                   ≈ℝ P *ℝ Q +ℝ (P *ℝ E₁ +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁))
            assocR = +ℝ-assoc (P *ℝ Q) (P *ℝ E₁) (E₁ *ℝ Q +ℝ E₁ *ℝ E₁)

            h₁ : P *ℝ Q <ℝ R +ℝ embedℚ d
            h₁ = ≈-<-resp (sub-add-cancelℝ (P *ℝ Q) (embedℚ d))
                    (<-+mono (P *ℝ Q -ℝ embedℚ d) R (embedℚ d)
                             (proj₁ (close n N₀≤n)))

            h₂ : R +ℝ embedℚ d ≤ℝ C +ℝ embedℚ d
            h₂ = ≤ℝ-+-mono {z = embedℚ d} (expPartialℝ-le-expℝ epq 0≤epq nn)

            b₁ : P *ℝ Q ≤ℝ C +ℝ embedℚ d
            b₁ = <⇒≤ℝ (<-≤ℝ-trans h₁ h₂)

            b₂ : P *ℝ E₁ ≤ℝ embedℚ (Kp * e₁)
            b₂ = ≤ℝ-resp-≈ (≈ℝ-refl) (≈ℝ-sym (embedℚ-* Kp e₁))
                   (*ℝ-≤-mono P (embedℚ Kp) E₁ (bndp n) 0≤E₁)

            b₃ : E₁ *ℝ Q ≤ℝ embedℚ (Kq * e₁)
            b₃ = ≤ℝ-resp-≈ (*ℝ-comm Q E₁) (≈ℝ-sym (embedℚ-* Kq e₁))
                   (*ℝ-≤-mono Q (embedℚ Kq) E₁ (bndq n) 0≤E₁)

            b₄ : E₁ *ℝ E₁ ≤ℝ embedℚ (e₁ * e₁)
            b₄ = ≈⇒≤ℝ (≈ℝ-sym (embedℚ-* e₁ e₁))

            s₁ : E₁ *ℝ Q +ℝ E₁ *ℝ E₁
                 ≤ℝ embedℚ (Kq * e₁) +ℝ embedℚ (e₁ * e₁)
            s₁ = ≤ℝ-trans (≤ℝ-+-mono {z = E₁ *ℝ E₁} b₃)
                    (≤ℝ-+-monoˡ {x = E₁ *ℝ E₁} {y = embedℚ (e₁ * e₁)}
                                {z = embedℚ (Kq * e₁)} b₄)

            s₂ : P *ℝ E₁ +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁)
                 ≤ℝ embedℚ (Kp * e₁)
                    +ℝ (embedℚ (Kq * e₁) +ℝ embedℚ (e₁ * e₁))
            s₂ = ≤ℝ-trans (≤ℝ-+-mono {z = E₁ *ℝ Q +ℝ E₁ *ℝ E₁} b₂)
                    (≤ℝ-+-monoˡ {z = embedℚ (Kp * e₁)} s₁)

            s₃ : P *ℝ Q +ℝ (P *ℝ E₁ +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁))
                 ≤ℝ (C +ℝ embedℚ d)
                    +ℝ (embedℚ (Kp * e₁)
                        +ℝ (embedℚ (Kq * e₁) +ℝ embedℚ (e₁ * e₁)))
            s₃ = ≤ℝ-trans (≤ℝ-+-mono {z = P *ℝ E₁ +ℝ (E₁ *ℝ Q +ℝ E₁ *ℝ E₁)} b₁)
                    (≤ℝ-+-monoˡ {z = C +ℝ embedℚ d} s₂)

            s : ℚ
            s = Kp * e₁ + (Kq * e₁ + e₁ * e₁)

            embSum : embedℚ (Kp * e₁) +ℝ (embedℚ (Kq * e₁) +ℝ embedℚ (e₁ * e₁))
                     ≈ℝ embedℚ s
            embSum = ≈ℝ-trans
                       (+ℝ-cong (≈ℝ-refl)
                                (≈ℝ-sym (embedℚ-+ (Kq * e₁) (e₁ * e₁))))
                       (≈ℝ-sym (embedℚ-+ (Kp * e₁) (Kq * e₁ + e₁ * e₁)))

            sq≤ : e₁ * e₁ ≤ e₁ * 1ℚ
            sq≤ = *-monoˡ-≤-nonNeg e₁ {{nonNegative 0≤e₁}} e₁≤1

            st₁ : Kp * e₁ + (Kq * e₁ + e₁ * e₁)
                  ≤ Kp * e₁ + (Kq * e₁ + e₁ * 1ℚ)
            st₁ = +-mono-≤ (≤-refl {Kp * e₁})
                    (+-mono-≤ (≤-refl {Kq * e₁}) sq≤)

            st₂ : Kp * e₁ + (Kq * e₁ + e₁ * 1ℚ)
                  ≡ (Kp * e₁ + Kq * e₁) + e₁ * 1ℚ
            st₂ = sym (+-assoc (Kp * e₁) (Kq * e₁) (e₁ * 1ℚ))

            grp : Kp * e₁ + Kq * e₁ ≡ (Kp + Kq) * e₁
            grp = sym (*-distribʳ-+ e₁ Kp Kq)

            st₃ : (Kp * e₁ + Kq * e₁) + e₁ * 1ℚ ≡ ((Kp + Kq) * e₁) + e₁
            st₃ = cong₂ _+_ grp (*-identityʳ e₁)

            st₄ : ((Kp + Kq) * e₁) + e₁ ≡ ((Kp + Kq) + 1ℚ) * e₁
            st₄ = trans (cong (λ z → ((Kp + Kq) * e₁) + z) (sym (*-identityˡ e₁)))
                        (sym (*-distribʳ-+ e₁ (Kp + Kq) 1ℚ))

            s≤c : s ≤ c * e₁
            s≤c = ≤-trans (≤-trans st₁ (≤-reflexive st₂))
                    (≤-trans (≤-reflexive st₃) (≤-reflexive st₄))

            s≤₁c : s ≤ e₁ * c
            s≤₁c = ≤-trans s≤c (≤-reflexive (*-comm c e₁))

            s<d : s < d
            s<d = ≤-<-trans s≤₁c shr

            budget : embedℚ s ≤ℝ embedℚ d
            budget = <⇒≤ℝ (embedℚ-mono s d s<d)

            s₄ : (C +ℝ embedℚ d)
                   +ℝ (embedℚ (Kp * e₁)
                       +ℝ (embedℚ (Kq * e₁) +ℝ embedℚ (e₁ * e₁)))
                 ≤ℝ (C +ℝ embedℚ d) +ℝ embedℚ d
            s₄ = ≤ℝ-+-monoˡ {z = C +ℝ embedℚ d}
                    (≤ℝ-trans (≈⇒≤ℝ embSum) budget)

            collapse : (C +ℝ embedℚ d) +ℝ embedℚ d ≈ℝ C +ℝ embedℚ e
            collapse = ≈ℝ-trans
                         (+ℝ-assoc C (embedℚ d) (embedℚ d))
                         (+ℝ-cong (≈ℝ-refl)
                           (≈ℝ-trans (≈ℝ-sym (embedℚ-+ d d))
                                     (embedℚ-cong (two-half e))))

            final : L ≤ℝ C +ℝ embedℚ e
            final = ≤ℝ-trans (≤ℝ-trans AB≤ (≈⇒≤ℝ expand))
                      (≤ℝ-trans (≈⇒≤ℝ assocR)
                        (≤ℝ-trans s₃
                          (≤ℝ-trans s₄ (≈⇒≤ℝ collapse))))
          in final
      in step (proj₁ idx)
             (proj₁ (proj₂ idx))
             (proj₁ (proj₂ (proj₂ idx)))
             (proj₂ (proj₂ (proj₂ idx)))
  in
    ≤ℝ-of-slack L C hyp

------------------------------------------------------------------------
-- The addition law at rational points
--
-- 有理点处的指数加法律

-- The two halves of the inequality close up by antisymmetry of the order.
--
-- 不等式的两半由序的反对称性合拢。
expℝ-add-rat : (p q : ℚ) (0≤p : 0ℚ ≤ p) (0≤q : 0ℚ ≤ q)
             → expℝ (embedℚ (p + q)) (embed-nonNeg (p + q) (≤-trans 0≤p (le-add-right p q 0≤q)))
               ≈ℝ expℝ (embedℚ p) (embed-nonNeg p 0≤p)
                  *ℝ expℝ (embedℚ q) (embed-nonNeg q 0≤q)
expℝ-add-rat p q 0≤p 0≤q =
  ≤ℝ-antisym (expℝ-add-rat-le p q 0≤p 0≤q) (expℝ-add-rat-ge p q 0≤p 0≤q)

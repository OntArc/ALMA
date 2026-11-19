------------------------------------------------------------------------
-- Algebraic Newtonian mechanics: skew-symmetry and right linearity
--
-- The quadratic Poisson quad-bracket is skew-symmetric:
--   {g, f} = - {f, g}.
-- Together with the left linearity of the previous slice this yields
-- linearity in the second argument, completing Q-bilinearity:
--   {f, g + h} = {f, g} + {f, h},
--   {f, r g}   = r {f, g}.
--
-- 代数版牛顿力学：反对称与右线性
--
-- 二次 Poisson 括号反对称：
--   {g, f} = - {f, g}。
-- 与上一切片的左线性结合，得到第二参数的线性，闭合 Q-双线性：
--   {f, g + h} = {f, g} + {f, h}，
--   {f, r g}   = r {f, g}。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Physics.Newton.QuadraticSkew where

open import Data.Rational using (_+_; _*_; -_)
open import Data.Rational.Properties using (+-comm; *-comm; neg-distrib-+; neg-distribʳ-*)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; cong; cong₂; module ≡-Reasoning)

open import Physics.Newton.Quadratic using
  (obs; quad-bracket; quad-add; quad-scale; quad-neg; twoℚ; fourℚ; mkObs)
open import Physics.Newton.QuadraticBilinear using (bracket-addˡ; bracket-scaleˡ)
open import Base.RationalRing using (foldNeg; neg4; rot4; rev4; flip3)

------------------------------------------------------------------------
-- Skew-symmetry
--
-- 反对称

-- {g, f} = - {f, g}.
bracket-skew : ∀ f g → quad-bracket g f ≡ quad-neg (quad-bracket f g)
bracket-skew (obs _ a b d e f) (obs _ a' b' d' e' f') =
  mkObs c-c q-c p-c d-c e-c f-c
  where
  -- Two-term coefficients: flip the factors of both products, then the
  -- positive and negative summands exchange by commutativity.
  --
  -- 两项系数：翻转两个乘积的因子，正、负加项再由交换律换位。
  c-c = let open ≡-Reasoning in begin
      a' * b + - (b' * a)
    ≡⟨ cong (λ t → t + - (b' * a)) (*-comm a' b) ⟩
      b * a' + - (b' * a)
    ≡⟨ cong (λ t → b * a' + - t) (*-comm b' a) ⟩
      b * a' + - (a * b')
    ≡⟨ +-comm (b * a') (- (a * b')) ⟩
      - (a * b') + b * a'
    ≡⟨ sym (foldNeg (a * b') (b * a')) ⟩
      - (a * b' + - (b * a')) ∎

  d-c = let open ≡-Reasoning in begin
      twoℚ * d' * e + - (twoℚ * e' * d)
    ≡⟨ cong (λ t → t + - (twoℚ * e' * d)) (flip3 twoℚ d' e) ⟩
      twoℚ * e * d' + - (twoℚ * e' * d)
    ≡⟨ cong (λ t → twoℚ * e * d' + - t) (flip3 twoℚ e' d) ⟩
      twoℚ * e * d' + - (twoℚ * d * e')
    ≡⟨ +-comm (twoℚ * e * d') (- (twoℚ * d * e')) ⟩
      - (twoℚ * d * e') + twoℚ * e * d'
    ≡⟨ sym (foldNeg (twoℚ * d * e') (twoℚ * e * d')) ⟩
      - (twoℚ * d * e' + - (twoℚ * e * d')) ∎

  e-c = let open ≡-Reasoning in begin
      fourℚ * d' * f + - (fourℚ * f' * d)
    ≡⟨ cong (λ t → t + - (fourℚ * f' * d)) (flip3 fourℚ d' f) ⟩
      fourℚ * f * d' + - (fourℚ * f' * d)
    ≡⟨ cong (λ t → fourℚ * f * d' + - t) (flip3 fourℚ f' d) ⟩
      fourℚ * f * d' + - (fourℚ * d * f')
    ≡⟨ +-comm (fourℚ * f * d') (- (fourℚ * d * f')) ⟩
      - (fourℚ * d * f') + fourℚ * f * d'
    ≡⟨ sym (foldNeg (fourℚ * d * f') (fourℚ * f * d')) ⟩
      - (fourℚ * d * f' + - (fourℚ * f * d')) ∎

  f-c = let open ≡-Reasoning in begin
      twoℚ * e' * f + - (twoℚ * f' * e)
    ≡⟨ cong (λ t → t + - (twoℚ * f' * e)) (flip3 twoℚ e' f) ⟩
      twoℚ * f * e' + - (twoℚ * f' * e)
    ≡⟨ cong (λ t → twoℚ * f * e' + - t) (flip3 twoℚ f' e) ⟩
      twoℚ * f * e' + - (twoℚ * e * f')
    ≡⟨ +-comm (twoℚ * f * e') (- (twoℚ * e * f')) ⟩
      - (twoℚ * e * f') + twoℚ * f * e'
    ≡⟨ sym (foldNeg (twoℚ * e * f') (twoℚ * f * e')) ⟩
      - (twoℚ * e * f' + - (twoℚ * f * e')) ∎

  -- Four-term coefficients: flip every product in place, then rotate the
  -- signed summands into the negated order.
  --
  -- 四项系数：原地翻转每个乘积，再将带符号加项旋转为取负后的次序。
  q-c = let open ≡-Reasoning in begin
      ((a' * e + twoℚ * d' * b) + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((t + twoℚ * d' * b) + - (e' * a))
                    + - (twoℚ * b' * d))
            (*-comm a' e) ⟩
      ((e * a' + twoℚ * d' * b) + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + t) + - (e' * a))
                    + - (twoℚ * b' * d))
            (flip3 twoℚ d' b) ⟩
      ((e * a' + twoℚ * b * d') + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + twoℚ * b * d') + t)
                    + - (twoℚ * b' * d))
            (cong -_ (*-comm e' a)) ⟩
      ((e * a' + twoℚ * b * d') + - (a * e')) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + twoℚ * b * d') + - (a * e')) + t)
            (cong -_ (flip3 twoℚ b' d)) ⟩
      ((e * a' + twoℚ * b * d') + - (a * e')) + - (twoℚ * d * b')
    ≡⟨ rot4 (e * a') (twoℚ * b * d') (- (a * e'))
                 (- (twoℚ * d * b')) ⟩
      ((- (a * e') + - (twoℚ * d * b')) + e * a')
        + twoℚ * b * d'
    ≡⟨ sym (neg4 (a * e') (twoℚ * d * b') (e * a')
                      (twoℚ * b * d')) ⟩
      - (((a * e' + twoℚ * d * b') + - (e * a'))
           + - (twoℚ * b * d')) ∎

  p-c = let open ≡-Reasoning in begin
      ((twoℚ * a' * f + e' * b) + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((t + e' * b) + - (b' * e))
                    + - (twoℚ * f' * a))
            (flip3 twoℚ a' f) ⟩
      ((twoℚ * f * a' + e' * b) + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + t) + - (b' * e))
                    + - (twoℚ * f' * a))
            (*-comm e' b) ⟩
      ((twoℚ * f * a' + b * e') + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + b * e') + t)
                    + - (twoℚ * f' * a))
            (cong -_ (*-comm b' e)) ⟩
      ((twoℚ * f * a' + b * e') + - (e * b')) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + b * e') + - (e * b')) + t)
            (cong -_ (flip3 twoℚ f' a)) ⟩
      ((twoℚ * f * a' + b * e') + - (e * b')) + - (twoℚ * a * f')
    ≡⟨ rev4 (twoℚ * f * a') (b * e') (- (e * b'))
                 (- (twoℚ * a * f')) ⟩
      ((- (twoℚ * a * f') + - (e * b')) + b * e')
        + twoℚ * f * a'
    ≡⟨ sym (neg4 (twoℚ * a * f') (e * b') (b * e')
                      (twoℚ * f * a')) ⟩
      - (((twoℚ * a * f' + e * b') + - (b * e'))
           + - (twoℚ * f * a')) ∎

------------------------------------------------------------------------
-- Negation distributes over addition and scaling of observables
--
-- 取负对观测量加法与数乘的分配

-- - (f + g) = - f + - g.
neg-add : ∀ f g → quad-neg (quad-add f g) ≡ quad-add (quad-neg f) (quad-neg g)
neg-add (obs c a b d e f) (obs c' a' b' d' e' f') =
  mkObs (neg-distrib-+ c c') (neg-distrib-+ a a') (neg-distrib-+ b b')
        (neg-distrib-+ d d') (neg-distrib-+ e e') (neg-distrib-+ f f')

-- - (r f) = r (- f).
--
-- - (r f) = r (- f)。
neg-scale : ∀ r f → quad-neg (quad-scale r f) ≡ quad-scale r (quad-neg f)
neg-scale r (obs c a b d e f) =
  mkObs (neg-distribʳ-* r c) (neg-distribʳ-* r a) (neg-distribʳ-* r b)
        (neg-distribʳ-* r d) (neg-distribʳ-* r e) (neg-distribʳ-* r f)

------------------------------------------------------------------------
-- Additive and scalar linearity in the second argument
--
-- 第二参数的加法与数乘线性

-- {f, g + h} = {f, g} + {f, h}.
bracket-addʳ : ∀ f g h →
               quad-bracket f (quad-add g h) ≡ quad-add (quad-bracket f g) (quad-bracket f h)
bracket-addʳ f g h = let open ≡-Reasoning in begin
    quad-bracket f (quad-add g h)
  ≡⟨ bracket-skew (quad-add g h) f ⟩
    quad-neg (quad-bracket (quad-add g h) f)
  ≡⟨ cong quad-neg (bracket-addˡ g h f) ⟩
    quad-neg (quad-add (quad-bracket g f) (quad-bracket h f))
  ≡⟨ neg-add (quad-bracket g f) (quad-bracket h f) ⟩
    quad-add (quad-neg (quad-bracket g f)) (quad-neg (quad-bracket h f))
  ≡⟨ cong₂ quad-add (sym (bracket-skew g f)) (sym (bracket-skew h f)) ⟩
    quad-add (quad-bracket f g) (quad-bracket f h) ∎

-- {f, r g} = r {f, g}.
bracket-scaleʳ : ∀ r f g →
                 quad-bracket f (quad-scale r g) ≡ quad-scale r (quad-bracket f g)
bracket-scaleʳ r f g = let open ≡-Reasoning in begin
    quad-bracket f (quad-scale r g)
  ≡⟨ bracket-skew (quad-scale r g) f ⟩
    quad-neg (quad-bracket (quad-scale r g) f)
  ≡⟨ cong quad-neg (bracket-scaleˡ r g f) ⟩
    quad-neg (quad-scale r (quad-bracket g f))
  ≡⟨ neg-scale r (quad-bracket g f) ⟩
    quad-scale r (quad-neg (quad-bracket g f))
  ≡⟨ cong (quad-scale r) (sym (bracket-skew g f)) ⟩
    quad-scale r (quad-bracket f g) ∎

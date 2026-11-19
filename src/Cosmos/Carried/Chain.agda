------------------------------------------------------------------------
-- Chains over ℕ with successor edges, and their composition
--
-- Shared by the finite-pushout and sequential colimit categories.
--
-- 后继边上的 ℕ 链及其复合
--
-- 由有限推送与序列余极限两个范畴共用。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.Chain where

open import Data.Nat.Base using (ℕ; suc)

-- Paths over successor edges; source is a parameter.
--
-- 后继边上的路径；源端为参数。
data Chain⇒ (m : ℕ) : ℕ → Set where
  stop : Chain⇒ m m
  step : ∀ {n} → Chain⇒ m n → Chain⇒ m (suc n)

-- Composition prepends f to g; it recurses on the target-built g.
--
-- 复合把 f 接到 g 前，对目标端构造的 g 递归。
infixl 7 _∘ch_
_∘ch_ : ∀ {m y n} → Chain⇒ y n → Chain⇒ m y → Chain⇒ m n
stop    ∘ch f = f
step g  ∘ch f = step (g ∘ch f)

-- The one-step successor arrow.
--
-- 一步后继箭头。
succ : ∀ {m} → Chain⇒ m (suc m)
succ = step stop

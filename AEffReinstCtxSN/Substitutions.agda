{-# OPTIONS --guardedness #-}

open import AEffReinstCtxSN.AEff
open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstCtxSN.Renamings
open import AEffReinstCtxSN.Types

open import Data.Product using (_×_)

open import Relation.Binary.PropositionalEquality hiding ([_])

module AEffReinstCtxSN.Substitutions where

-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ → Γ' ⊢V⦂ X


-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : {Γ : Ctx} → Sub Γ Γ
id-subst x = ` x

_[_]s : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x


-- LIFTING SUBSTITUTIONS

lift : {Γ Γ' : Ctx} {X : VType} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)


-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

mutual

  infix 40 _[_]v
  infix 40 _[_]m

  _[_]v : {Γ Γ' : Ctx} → {X : VType} → Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X
  (` x) [ s ]v =
    s x
  (`` c) [ s ]v =
    `` c
  (ƛ M) [ s ]v =
    ƛ (M [ lift s ]m)
  ⟨ V ⟩ [ s ]v =
    ⟨ V [ s ]v ⟩

  _[_]m : {Γ Γ' : Ctx} → {Δ : RCtx} {C : CType} → Γ ∣ Δ ⊢M⦂ C → Sub Γ Γ'  → Γ' ∣ Δ ⊢M⦂ C
  (return V) [ s ]m =
    return (V [ s ]v)
  (let= M `in N) [ s ]m =
    let= (M [ s ]m) `in (N [ lift s ]m)
  (V · W) [ s ]m =
    (V [ s ]v) · (W [ s ]v)
  reinstall [ s ]m =
    reinstall
  (↑ op p V M) [ s ]m =
    ↑ op p (V [ s ]v) (M [ s ]m)
  (↓ op V M) [ s ]m =
    ↓ op (V [ s ]v) (M [ s ]m)
  (promise op ∣ p ↦ M `in N) [ s ]m =
    promise op ∣ p ↦ (M [ lift s ]m) `in (N [ lift s ]m)
  (await V until M) [ s ]m =
    await (V [ s ]v) until (M [ lift s ]m)
  (coerce p q M) [ s ]m =
    coerce p q (M [ s ]m)


-- REINSTALL SUBSTITUTION: REPLACING THE FREE OCCURRENCES OF reinstall
-- (THOSE NOT INSIDE NESTED HANDLER CODE, let-BOUND COMPUTATIONS,
-- OR BODIES OF INTERRUPTS) BY A COMPUTATION R

infix 40 _[_]r

_[_]r : {Γ : Ctx} {X : VType} {oi : O × I} {C : CType} →
        Γ ∣ re X oi ⊢M⦂ C → Γ ⊢M⦂ ⟨ X ⟩ ! oi → Γ ⊢M⦂ C
(return V) [ R ]r =
  return V
(V · W) [ R ]r =
  V · W
reinstall [ R ]r =
  R
(let= M `in N) [ R ]r =
  let= M `in (N [ M-rename wk₁ R ]r)
(↑ op p V M) [ R ]r =
  ↑ op p V (M [ R ]r)
(↓ op V M) [ R ]r =
  ↓ op V M
(promise op ∣ p ↦ M `in N) [ R ]r =
  promise op ∣ p ↦ M `in (N [ M-rename wk₁ R ]r)
(await V until M) [ R ]r =
  await V until (M [ M-rename wk₁ R ]r)
(coerce p q M) [ R ]r =
  coerce p q (M [ R ]r)


-- ACTION OF SUBSTITUTION ON WELL-TYPED PROCESSES

infix 40 _[_]p

_[_]p : {Γ Γ' : Ctx} {o : O} {PP : PType o} → Γ ⊢P⦂ PP → Sub Γ Γ' → Γ' ⊢P⦂ PP
(run M) [ s ]p =
  run (M [ s ]m)
(P ∥ Q) [ s ]p =
  (P [ s ]p) ∥ (Q [ s ]p)
(↑ op p V P) [ s ]p =
  ↑ op p (V [ s ]v) (P [ s ]p)
(↓ op V P) [ s ]p =
  ↓ op (V [ s ]v) (P [ s ]p)
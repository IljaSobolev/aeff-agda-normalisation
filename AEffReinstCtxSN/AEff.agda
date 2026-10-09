{-# OPTIONS --guardedness #-}

open import Data.Maybe
open import Data.Product hiding (Σ)

open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Negation

open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstCtxSN.Types

module AEffReinstCtxSN.AEff where

-- ARITY ASSIGNMENT TO SIGNATURES OF SIGNALS, INTERRUPTS, AND BASE CONSTANTS

postulate payload : Σₛ → GType     -- payload type assignment for signal and interrupt names

postulate Σ-base : Set             -- set of base constants
postulate ar-base : Σ-base → BType -- arity assignment to base constants


-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A


-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList VType

data _∈_ (X : VType) : Ctx → Set where
  Hd : {Γ : Ctx} → X ∈ (Γ ∷ X)
  Tl : {Γ : Ctx} {Y : VType} → X ∈ Γ → X ∈ (Γ ∷ Y)


-- REINSTALL CONTEXTS: ∅ OUTSIDE OF REINSTALLABLE HANDLER CODE, re X (o , i)
-- INSIDE THE CODE OF A HANDLER WHOSE PROMISE TYPE IS ⟨ X ⟩, WHERE reinstall
-- (REINSTALLING THE HANDLER) HAS THE COMPUTATION TYPE ⟨ X ⟩ ! (o , i)
-- (reinstall CANNOT BE USED UNDER INTERRUPTS OR IN FUNCTION BODIES,
-- AS BODIES OF ↓ AND ƛ ARE TYPED IN THE EMPTY REINSTALL CONTEXT ∅)

data RCtx : Set where
  ∅  : RCtx
  re : VType → O × I → RCtx


-- EFFECT OF REINSTALLING A HANDLER FOR op WHOSE CODE HAS EFFECT (o' , i')

reinst-eff : Σₛ → O → I → O × I
reinst-eff op o' i' = ∅ₒ , (∅ᵢ [ op ↦ just (o' , i') ]ᵢ)


-- DERIVATIONS OF WELL-TYPED TERMS

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where
  
    `_  : {X : VType} →
          X ∈ Γ →
          -------------
          Γ ⊢V⦂ X
          
    ``_  : (c : Σ-base) →
          --------------
          Γ ⊢V⦂ ```(ar-base c)
          
    ƛ   : {X : VType}
          {C : CType} →
          Γ ∷ X ∣ ∅ ⊢M⦂ C → 
          -------------
          Γ ⊢V⦂ X ⇒ C

    ⟨_⟩ : {X : VType} →
          Γ ⊢V⦂ X →
          -------------
          Γ ⊢V⦂ ⟨ X ⟩
          
  infix 40 _·_

  data _∣_⊢M⦂_ (Γ : Ctx) : RCtx → CType → Set where

    return           : {Δ : RCtx}
                       {X : VType}
                       {o : O}
                       {i : I} →
                       Γ ⊢V⦂ X →
                       -----------------
                       Γ ∣ Δ ⊢M⦂ X ! (o , i)

    let=_`in_        : {Δ : RCtx}
                       {X Y : VType}
                       {o : O}
                       {i : I} → 
                       Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                       Γ ∷ X ∣ Δ ⊢M⦂ Y ! (o , i) →
                       -----------------------
                       Γ ∣ Δ ⊢M⦂ Y ! (o , i)

    _·_              : {Δ : RCtx}
                       {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ X ⇒ C →
                       Γ ⊢V⦂ X →
                       -------------
                       Γ ∣ Δ ⊢M⦂ C

    reinstall        : {X : VType}
                       {o : O}
                       {i : I} →
                       -----------------------------------------
                       Γ ∣ re X (o , i) ⊢M⦂ ⟨ X ⟩ ! (o , i)

    ↑                : {Δ : RCtx}
                       {X : VType}
                       {o : O}
                       {i : I} →
                       (op : Σₛ) →
                       op ∈ₒ o →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ∣ Δ ⊢M⦂ X ! (o , i)

    ↓                : {Δ : RCtx}
                       {X : VType}
                       {o : O}
                       {i : I}
                       (op : Σₛ) →
                       Γ ⊢V⦂ ```(payload op) →
                       Γ ∣ ∅ ⊢M⦂ X ! (o , i) →
                       ----------------------
                       Γ ∣ Δ ⊢M⦂ X ! op ↓ₑ (o , i)

    promise_∣_↦_`in_ : {Δ : RCtx}
                       {X Y : VType}
                       {o o' : O}
                       {i i' : I} → 
                       (op : Σₛ) →
                       just (o' , i') ⊑-aux imap i op →
                       Γ ∷ ```(payload op) ∣ re X (reinst-eff op o' i') ⊢M⦂ ⟨ X ⟩ ! (o' , i') →
                       Γ ∷ ⟨ X ⟩ ∣ Δ ⊢M⦂ Y ! (o , i) →
                       ------------------------------------------
                       Γ ∣ Δ ⊢M⦂ Y ! (o , i)

    await_until_     : {Δ : RCtx}
                       {X : VType}
                       {C : CType} → 
                       Γ ⊢V⦂ ⟨ X ⟩ →
                       Γ ∷ X ∣ Δ ⊢M⦂ C →
                       --------------
                       Γ ∣ Δ ⊢M⦂ C

    coerce           : {Δ : RCtx}
                       {X : VType}
                       {o o' : O}
                       {i i' : I} →
                       o ⊑ₒ o' →
                       i ⊑ᵢ i' → 
                       Γ ∣ Δ ⊢M⦂ X ! (o , i) →
                       -------------------
                       Γ ∣ Δ ⊢M⦂ X ! (o' , i')


-- COMPUTATIONS OUTSIDE OF HANDLER CODE

_⊢M⦂_ : Ctx → CType → Set
Γ ⊢M⦂ C = Γ ∣ ∅ ⊢M⦂ C
                        

-- DERIVATIONS OF WELL-TYPED PROCESSES

infix 10 _⊢P⦂_

data _⊢P⦂_ (Γ : Ctx) : {o : O} → PType o → Set where

  run     : {X : VType}
            {o : O}
            {i : I} →
            Γ ⊢M⦂ X ! (o , i) →
            -------------------
            Γ ⊢P⦂ X ‼ o , i

  _∥_     : {o o' : O}
            {PP : PType o} →
            {QQ : PType o'} → 
            Γ ⊢P⦂ PP →
            Γ ⊢P⦂ QQ →
            --------------
            Γ ⊢P⦂ (PP ∥ QQ)

  ↑       : {o : O} →
            {PP : PType o}
            (op : Σₛ) →
            op ∈ₒ o →
            Γ ⊢V⦂ ```(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ PP

  ↓       : {o : O}
            {PP : PType o}
            (op : Σₛ) →
            Γ ⊢V⦂ ```(payload op) →
            Γ ⊢P⦂ PP →
            ----------------------
            Γ ⊢P⦂ op ↓ₚ PP
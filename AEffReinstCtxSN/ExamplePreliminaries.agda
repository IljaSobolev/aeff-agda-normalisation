{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstCtxSN.Types
open import AEffReinstCtxSN.AEff
open import AEffReinstCtxSN.Preservation

module AEffReinstCtxSN.ExamplePreliminaries where

-- A SINGLETON SIGNAL ANNOTATION

[_]ₒ : Σₛ → O
[ op ]ₒ = omap (λ op' → if op ≡ op' then just tt else nothing)

∈-[]ₒ : op ∈ₒ [ op ]ₒ
∈-[]ₒ = ite-≡

∅ₒ-⊑ₒ : ∅ₒ ⊑ₒ o
∅ₒ-⊑ₒ op ()


-- THE RECURSIVE INTERRUPT ANNOTATION loop op o = { op ↦ (o , loop op o) }
-- OF A HANDLER FOR op THAT ISSUES THE SIGNALS IN o AND THEN REINSTALLS ITSELF

loop : Σₛ → O → I
imap (loop op o) op' with decₛ op op'
... | yes _ = just (o , loop op o)
... | no  _ = nothing


-- THE ANNOTATION OF reinstall IN THE CODE OF SUCH A HANDLER IS INCLUDED IN loop op o,
-- AND loop op o PROVIDES THE ANNOTATION OF THE HANDLER CODE AT op

loop-⊑ᵢ : (∅ᵢ [ op ↦ just (o , loop op o) ]ᵢ) ⊑ᵢ loop op o
rel (loop-⊑ᵢ {op = op}) op' with decₛ op op'
... | yes _ = ⊑ₒ-refl , ⊑ᵢ-refl
... | no  _ = tt

loop-hit : just (o , loop op o) ⊑-aux imap (loop op o) op
loop-hit {op = op} with decₛ op op
... | yes _ = ⊑ₒ-refl , ⊑ᵢ-refl
... | no ¬p = ⊥-elim (¬p refl)


-- THE RECURSIVE INTERRUPT ANNOTATION two op o op' m = { op ↦ (o , two op o op' m) , op' ↦ m }
-- OF A REINSTALLABLE HANDLER FOR op WHOSE CODE INSTALLS A HANDLER FOR op' WITH ANNOTATION m

two : Σₛ → O → Σₛ → Maybe (O × I) → I
imap (two op o op' m) op'' with decₛ op op''
... | yes _ = just (o , two op o op' m)
... | no  _ with decₛ op' op''
...   | yes _ = m
...   | no  _ = nothing

two-⊑ᵢ : {m : Maybe (O × I)} →
         ------------------------------------------------
         (∅ᵢ [ op ↦ just (o , two op o op' m) ]ᵢ) ⊑ᵢ two op o op' m
rel (two-⊑ᵢ {op = op}) op'' with decₛ op op''
... | yes _ = ⊑ₒ-refl , ⊑ᵢ-refl
... | no  _ = tt

two-hit : {m : Maybe (O × I)} →
          ------------------------------------------
          just (o , two op o op' m) ⊑-aux imap (two op o op' m) op
two-hit {op = op} with decₛ op op
... | yes _ = ⊑ₒ-refl , ⊑ᵢ-refl
... | no ¬p = ⊥-elim (¬p refl)

two-hit' : {m : Maybe (O × I)} →
           op ≢ op' →
           ---------------------------
           m ⊑-aux imap (two op o op' m) op'
two-hit' {op = op} {op' = op'} {m = m} p with decₛ op op'
... | yes q = ⊥-elim (p q)
... | no  _ with decₛ op' op'
...   | yes _ = ⊑-aux-refl m
...   | no ¬q = ⊥-elim (¬q refl)


-- THE EMPTY INTERRUPT ANNOTATION IS THE LEAST ONE

∅ᵢ-⊑ᵢ : ∅ᵢ ⊑ᵢ i
rel ∅ᵢ-⊑ᵢ op = tt


-- REFLEXIVE-TRANSITIVE CLOSURE OF THE REDUCTION RELATION

infixr 5 _∷*_
infix 4 _↝*_

data _↝*_ {Γ : Ctx} {C : CType} : Γ ⊢M⦂ C → Γ ⊢M⦂ C → Set where

  []*  : {M : Γ ⊢M⦂ C} →
         ------
         M ↝* M

  _∷*_ : {M M' M'' : Γ ⊢M⦂ C} →
         M ↝ M' →
         M' ↝* M'' →
         -----------
         M ↝* M''

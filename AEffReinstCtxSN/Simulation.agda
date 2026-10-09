{-# OPTIONS --guardedness #-}

open import Data.Nat using (_<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using () renaming ([] to []ₗ; _∷_ to _∷ₗ_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Induction.WellFounded using (Acc; acc)

open import AEffReinstCtxSN.Types
open import AEffReinstCtxSN.AEff
open import AEffReinstCtxSN.Preservation
open import AEffReinstCtxSN.Finality
open import AEffReinstCtxSN.Renamings
open import AEffReinstCtxSN.Substitutions
open import AEffReinstSN.CoinductiveEffectAnnotations

open import AEffReinstCtxSN.AEffReinstCtxBaseSN.StronglyNormalising using () renaming (SN to SN*; sn to sn*)
open import AEffReinstCtxSN.AEffReinstCtxBaseSN.Main using () renaming (strong-norm to strong-norm*)
open import AEff.Simulation using (ContextShape; [-]; coe; other; _↝c_; coe-ctx; other-ctx; coe-[-]; coe-↓; ∣_∣; size-mono-↝)

import AEffReinstCtxSN.AEffReinstCtxBaseSN.AEff as B

module AEffReinstCtxSN.Simulation where

-- EMBEDDING OF EFFECT-TYPED TYPES, CONTEXTS, VARIABLES AND TERMS
-- INTO THE SKELETAL REINSTALL-CONTEXT CALCULUS (ERASING EFFECTS AND COERCIONS)

emb-ty-v : VType → B.Type

emb-ty-c : CType → B.Type

emb-ty-v (``` x) = B.``` x
emb-ty-v (X ⇒ Y) = emb-ty-v X B.⇒ emb-ty-c Y
emb-ty-v ⟨ V ⟩ = B.⟨ emb-ty-v V ⟩

emb-ty-c (X ! _) = emb-ty-v X

emb-rctx : RCtx → B.RCtx
emb-rctx ∅ = B.∅
emb-rctx (re X _) = B.re (emb-ty-v X)

emb-ctx : Ctx → B.Ctx
emb-ctx [] = B.[]
emb-ctx (Γ ∷ X) = emb-ctx Γ B.∷ emb-ty-v X

emb-∈ : {Γ : Ctx} {X : VType} → X ∈ Γ → emb-ty-v X B.∈ emb-ctx Γ
emb-∈ Hd = B.Hd
emb-∈ (Tl x) = B.Tl (emb-∈ x)

emb-tm-v : {Γ : Ctx} {X : VType} → Γ ⊢V⦂ X → emb-ctx Γ B.⊢V⦂ emb-ty-v X

emb-tm-m : {Γ : Ctx} {Δ : RCtx} {X : CType} → Γ ∣ Δ ⊢M⦂ X → emb-ctx Γ B.∣ emb-rctx Δ ⊢M⦂ emb-ty-c X

emb-tm-v (` x) = B.` (emb-∈ x)
emb-tm-v (`` c) = B.`` c
emb-tm-v (ƛ M) = B.ƛ (emb-tm-m M)
emb-tm-v ⟨ V ⟩ = B.⟨ emb-tm-v V ⟩

emb-tm-m (return V) = B.return (emb-tm-v V)
emb-tm-m (let= M `in N) = B.let= emb-tm-m M `in emb-tm-m N
emb-tm-m (V · W) = emb-tm-v V B.· emb-tm-v W
emb-tm-m reinstall = B.reinstall
emb-tm-m (↑ op p V M) = B.↑ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (↓ op V M) = B.↓ op (emb-tm-v V) (emb-tm-m M)
emb-tm-m (promise op ∣ p ↦ M `in N) = B.promise op ↦ emb-tm-m M `in emb-tm-m N
emb-tm-m (await V until M) = B.await emb-tm-v V until emb-tm-m M
emb-tm-m (coerce p q M) = emb-tm-m M


-- RELATION BETWEEN EFFECT-TYPED RENAMINGS AND SKELETAL RENAMINGS

infix 4 _~ᵣ_
_~ᵣ_ : {Γ Γ' : Ctx} (r : Ren Γ Γ') (r† : B.Ren (emb-ctx Γ) (emb-ctx Γ')) → Set
_~ᵣ_ {Γ} r r† = {X : VType} (x : X ∈ Γ) → emb-∈ (r x) ≡ r† (emb-∈ x)


-- RELATION BETWEEN EFFECT-TYPED SUBSTITUTIONS AND SKELETAL SUBSTITUTIONS

infix 4 _~ₛ_
_~ₛ_ : {Γ Γ' : Ctx} (s : Sub Γ Γ') (s† : B.Sub (emb-ctx Γ) (emb-ctx Γ')) → Set
_~ₛ_ {Γ} s s† = {X : VType} (x : X ∈ Γ) → emb-tm-v (s x) ≡ s† (emb-∈ x)


-- RELATED RENAMINGS ACT THE SAME ON RELATED TERMS

~ᵣ-v : {Γ Γ' : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
       {r : Ren Γ Γ'} {r† : B.Ren (emb-ctx Γ) (emb-ctx Γ')} →
       r ~ᵣ r† →
       ------------
       emb-tm-v (V-rename r V) ≡ B.V-rename r† (emb-tm-v V)

~ᵣ-m : {Γ Γ' : Ctx} {Δ : RCtx} {X : CType} (M : Γ ∣ Δ ⊢M⦂ X)
       {r : Ren Γ Γ'} {r† : B.Ren (emb-ctx Γ) (emb-ctx Γ')} →
       r ~ᵣ r† →
       ------------
       emb-tm-m (M-rename r M) ≡ B.M-rename r† (emb-tm-m M)

~ᵣ-lift : {Γ Γ' : Ctx} {Δ : RCtx} {X : VType} {Y : CType} (M : Γ ∷ X ∣ Δ ⊢M⦂ Y)
          {r : Ren Γ Γ'} {r† : B.Ren (emb-ctx Γ) (emb-ctx Γ')} →
          r ~ᵣ r† →
          ------------
          emb-tm-m (M-rename (wk₂ r) M) ≡ B.M-rename (B.wk₂ r†) (emb-tm-m M)

~ᵣ-lift M ~r = ~ᵣ-m M (λ {Hd → refl; (Tl x) → cong B.Tl (~r x)})

~ᵣ-v (` x) ~r = cong B.`_ (~r x)
~ᵣ-v (`` c) ~r = refl
~ᵣ-v (ƛ M) ~r = cong B.ƛ (~ᵣ-lift M ~r)
~ᵣ-v ⟨ V ⟩ ~r = cong B.⟨_⟩ (~ᵣ-v V ~r)

~ᵣ-m (return V) ~r = cong B.return (~ᵣ-v V ~r)
~ᵣ-m (let= M `in N) ~r = cong₂ B.let=_`in_ (~ᵣ-m M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (V · W) ~r = cong₂ B._·_ (~ᵣ-v V ~r) (~ᵣ-v W ~r)
~ᵣ-m reinstall ~r = refl
~ᵣ-m (↑ op p V M) ~r = cong₂ (B.↑ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (↓ op V M) ~r = cong₂ (B.↓ op) (~ᵣ-v V ~r) (~ᵣ-m M ~r)
~ᵣ-m (promise op ∣ p ↦ M `in N) ~r = cong₂ (B.promise op ↦_`in_) (~ᵣ-lift M ~r) (~ᵣ-lift N ~r)
~ᵣ-m (await V until M) ~r = cong₂ B.await_until_ (~ᵣ-v V ~r) (~ᵣ-lift M ~r)
~ᵣ-m (coerce p q M) ~r = ~ᵣ-m M ~r


-- RELATED SUBSTITUTIONS ACT THE SAME ON RELATED TERMS

~ₛ-v : {Γ Γ' : Ctx} {X : VType} (V : Γ ⊢V⦂ X)
       {s : Sub Γ Γ'} {s† : B.Sub (emb-ctx Γ) (emb-ctx Γ')} →
       s ~ₛ s† →
       ------------
       emb-tm-v (V [ s ]v) ≡ (emb-tm-v V) B.[ s† ]v

~ₛ-m : {Γ Γ' : Ctx} {Δ : RCtx} {X : CType} (M : Γ ∣ Δ ⊢M⦂ X)
       {s : Sub Γ Γ'} {s† : B.Sub (emb-ctx Γ) (emb-ctx Γ')} →
       s ~ₛ s† →
       ------------
       emb-tm-m (M [ s ]m) ≡ (emb-tm-m M) B.[ s† ]m

~ₛ-lift : {Γ Γ' : Ctx} {Δ : RCtx} {X : VType} {Y : CType} (M : Γ ∷ X ∣ Δ ⊢M⦂ Y)
          {s : Sub Γ Γ'} {s† : B.Sub (emb-ctx Γ) (emb-ctx Γ')} →
          s ~ₛ s† →
          ------------
          emb-tm-m (M [ lift s ]m) ≡ (emb-tm-m M) B.[ B.lift s† ]m

~ₛ-lift M ~s = ~ₛ-m M (λ {Hd → refl; (Tl x) → trans (~ᵣ-v _ (λ _ → refl)) (cong (B.V-rename B.Tl) (~s x))})

~ₛ-v (` x) ~s = ~s x
~ₛ-v (`` c) ~s = refl
~ₛ-v (ƛ M) ~s = cong B.ƛ (~ₛ-lift M ~s)
~ₛ-v ⟨ V ⟩ ~s = cong B.⟨_⟩ (~ₛ-v V ~s)

~ₛ-m (return V) ~s = cong B.return (~ₛ-v V ~s)
~ₛ-m (let= M `in N) ~s = cong₂ B.let=_`in_ (~ₛ-m M ~s) (~ₛ-lift N ~s)
~ₛ-m (V · W) ~s = cong₂ B._·_ (~ₛ-v V ~s) (~ₛ-v W ~s)
~ₛ-m reinstall ~s = refl
~ₛ-m (↑ op p V M) ~s = cong₂ (B.↑ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (↓ op V M) ~s = cong₂ (B.↓ op) (~ₛ-v V ~s) (~ₛ-m M ~s)
~ₛ-m (promise op ∣ p ↦ M `in N) ~s = cong₂ (B.promise op ↦_`in_) (~ₛ-lift M ~s) (~ₛ-lift N ~s)
~ₛ-m (await V until M) ~s = cong₂ B.await_until_ (~ₛ-v V ~s) (~ₛ-lift M ~s)
~ₛ-m (coerce p q M) ~s = ~ₛ-m M ~s


-- FURTHER IDENTITIES ABOUT RELATED RENAMINGS, SUBSTITUTIONS AND TERMS

~ᵣ-wk₁-v : {Γ : Ctx} {X Z : VType}
           (V : Γ ⊢V⦂ X) →
           -----------
           emb-tm-v (V-rename (wk₁ {X = Z}) V) ≡ B.V-rename (B.wk₁) (emb-tm-v V)
             
~ᵣ-wk₁-v V = ~ᵣ-v V (λ _ → refl)

~ᵣ-wk₁-m : {Γ : Ctx} {Δ : RCtx} {Z : VType} {Y : CType}
           (M : Γ ∣ Δ ⊢M⦂ Y) →
           -----------
           emb-tm-m (M-rename (wk₁ {X = Z}) M) ≡ B.M-rename (B.wk₁) (emb-tm-m M)
             
~ᵣ-wk₁-m M = ~ᵣ-m M (λ _ → refl)

~ᵣ-wk₂-wk₁-m : {Γ : Ctx} {X Z : VType} {Y : CType}
               (M : Γ ∷ X ⊢M⦂ Y) →
               -----------
               emb-tm-m (M-rename (wk₂ (wk₁ {X = Z})) M) ≡ B.M-rename (B.wk₂ B.wk₁) (emb-tm-m M)

~ᵣ-wk₂-wk₁-m M = ~ᵣ-m M (λ {Hd → refl; (Tl x) → refl})

~ₛᵣ-m  : {Γ : Ctx} {Δ : RCtx} {X : VType} {Y : CType}
         (M : Γ ∷ X ∣ Δ ⊢M⦂ Y) (V : Γ ⊢V⦂ X) →
         -----------
         emb-tm-m (M [ id-subst [ V ]s ]m) ≡ (emb-tm-m M) B.[ B.id-subst B.[ emb-tm-v V ]s ]m

~ₛᵣ-m  M V = ~ₛ-m M (λ {Hd → refl; (Tl x) → refl})

~-strengthen : {Γ : Ctx} {X : VType} {A : BType}
               (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A) →
               -----------------------
               emb-tm-v (strengthen-val {Δ = X ∷ₗ []ₗ} V) ≡ B.strengthen-val (emb-tm-v V)

~-strengthen (` Tl x) = refl
~-strengthen (`` c) = refl


-- ERASURE COMMUTES WITH REINSTALL SUBSTITUTION

~-[]r : {Γ : Ctx} {X : VType} {oi : O × I} {C : CType}
        (M : Γ ∣ re X oi ⊢M⦂ C) (R : Γ ⊢M⦂ ⟨ X ⟩ ! oi) →
        ------------------------------------------------
        emb-tm-m (M [ R ]r) ≡ (emb-tm-m M) B.[ emb-tm-m R ]r

~-[]r (return V) R = refl
~-[]r (V · W) R = refl
~-[]r reinstall R = refl
~-[]r (let= M `in N) R =
  cong₂ B.let=_`in_ (~-[]r M R) (trans (~-[]r N (M-rename wk₁ R)) (cong (emb-tm-m N B.[_]r) (~ᵣ-wk₁-m R)))
~-[]r (↑ op p V M) R =
  cong (B.↑ op (emb-tm-v V)) (~-[]r M R)
~-[]r (↓ op V M) R = refl
~-[]r (promise op ∣ p ↦ M `in N) R =
  cong (B.promise op ↦ emb-tm-m M `in_) (trans (~-[]r N (M-rename wk₁ R)) (cong (emb-tm-m N B.[_]r) (~ᵣ-wk₁-m R)))
~-[]r (await V until M) R =
  cong (B.await emb-tm-v V until_) (trans (~-[]r M (M-rename wk₁ R)) (cong (emb-tm-m M B.[_]r) (~ᵣ-wk₁-m R)))
~-[]r (coerce p q M) R = ~-[]r M R


-- FINDING THE CONTEXT SHAPE OF A TERM

ctx-shape-of : {Γ : Ctx} {X : CType} → Γ ⊢M⦂ X → ContextShape
ctx-shape-of (return _) = [-]
ctx-shape-of (let= M `in _) = other (ctx-shape-of M)
ctx-shape-of (_ · _) = [-]
ctx-shape-of (↑ _ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (↓ _ _ M) = other (ctx-shape-of M)
ctx-shape-of (promise _ ∣ _ ↦ _ `in N) = other (ctx-shape-of N)
ctx-shape-of (await _ until M) = [-]
ctx-shape-of (coerce _ _ M) = coe (ctx-shape-of M)


-- THE SIMULATION RESULT: A REDUCTION IN THE EFFECT-TYPED CALCULUS
-- EITHER CORRESPONDS TO A REDUCTION IN THE SKELETAL CALCULUS,
-- OR IT IS A REDUCTION OF THE CONTEXT SHAPE

sim : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
      M ↝↝ N →
      ------------------------
      emb-tm-m M B.↝↝ emb-tm-m N ⊎
      (emb-tm-m M ≡ emb-tm-m N)
        × ctx-shape-of M ↝c ctx-shape-of N

sim (apply M V) rewrite ~ₛᵣ-m M V = inj₁ (B.apply _ _)
sim (let-return V N) rewrite ~ₛᵣ-m N V = inj₁ (B.let-return _ _)
sim (let-↑ p V M N) = inj₁ (B.let-↑ _ _ _)
sim (let-promise {X} p M₁ M₂ N) rewrite ~ᵣ-wk₂-wk₁-m {Z = ⟨ X ⟩} N = inj₁ (B.let-promise _ _ _)
sim (let-await {X} V M N) rewrite ~ᵣ-wk₂-wk₁-m {Z = X} N = inj₁ (B.let-await _ _ _)
sim (promise-↑ p r V M N) rewrite ~-strengthen V = inj₁ (B.promise-↑ _ _ _)
sim (↓-return V W) = inj₁ (B.↓-return _ _)
sim (↓-↑ p V W M) = inj₁ (B.↓-↑ _ _ _)
sim (↓-promise-op {X} p V M N)
  rewrite ~-[]r (M [ id-subst [ V ]s ]m) (reinst-handler M) |
  ~ₛᵣ-m M V |
  ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V =
  inj₁ (B.↓-promise-op _ _ _)
sim (↓-promise-op' {X} p q V M N) rewrite ~ᵣ-wk₁-v {Z = ⟨ X ⟩} V = inj₁ (B.↓-promise-op' (λ z → p (sym z)) _ _ _)
sim (↓-await {X} V M N) rewrite ~ᵣ-wk₁-v {Z = X} V = inj₁ (B.↓-await _ _ _)
sim (await-promise V M) rewrite ~ₛᵣ-m M V = inj₁ (B.await-promise _ _)
sim (context-let r) with sim r
... | inj₁ r = inj₁ (B.context-let r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↑ r) with sim r
... | inj₁ r = inj₁ (B.context-↑ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-↓ r) with sim r
... | inj₁ r = inj₁ (B.context-↓ r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-promise r) with sim r
... | inj₁ r = inj₁ (B.context-promise r)
... | inj₂ (e , r) rewrite e = inj₂ (refl , other-ctx r)
sim (context-coerce r) with sim r
... | inj₁ r = inj₁ r
... | inj₂ (e , r) rewrite e = inj₂ (refl , coe-ctx r)
sim (coerce-return V) = inj₂ (refl , coe-[-])
sim (coerce-↑ r V M) = inj₂ (refl , coe-↓)
sim (coerce-promise r M N) = inj₂ (refl , coe-↓)
sim (coerce-await V M) = inj₂ (refl , coe-[-])


-- STRONG NORMALISATION PROOF BY MEANS OF THE SIMULATION AND
-- WELL-FOUNDEDNESS OF CONTEXT SHAPE REDUCTION

data SN {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) : Set where
  sn : ({N : Γ ⊢M⦂ X} → M ↝↝ N → SN N) → SN M

sn*→sn : {Γ : Ctx} {X : CType} {M N : Γ ⊢M⦂ X} →
         Acc _<_ ∣ ctx-shape-of M ∣ →
         --------------------------------
         SN* (emb-tm-m M) → M ↝↝ N → SN N

sn*→sn aM sM r with sim r
sn*→sn aM (sn* f) _ | inj₁ r = sn (sn*→sn (<-wellFounded _) (f r))
sn*→sn (acc aM) sM _ | inj₂ (e , r) rewrite e = sn (sn*→sn (aM (size-mono-↝ r)) sM)

strong-norm : {Γ : Ctx} {X : CType} (M : Γ ⊢M⦂ X) → SN M
strong-norm M = sn (sn*→sn (<-wellFounded _) (strong-norm* (emb-tm-m M)))

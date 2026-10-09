{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstCtxSN.Types
open import AEffReinstCtxSN.AEff
open import AEffReinstCtxSN.Renamings
open import AEffReinstCtxSN.Substitutions
open import AEffReinstCtxSN.Preservation
open import AEffReinstCtxSN.ExamplePreliminaries
open import AEffReinstCtxSN.Finality using (_↝↝_; ↝-to-↝↝; context-promise)

module AEffReinstCtxSN.Counterexamples where

-- RAW (UNTYPED) TERMS WITH DE BRUIJN INDICES, IN WHICH reinstall IS AN ORDINARY
-- COMPUTATION THAT IS ALLOWED TO APPEAR ANYWHERE (COERCIONS ARE NOT REPRESENTED)

data RV : Set

data RC : Set

data RV where
  rvar   : ℕ → RV
  rconst : Σ-base → RV
  rƛ     : RC → RV
  r⟨_⟩   : RV → RV

infix 40 _r·_

data RC where
  rreturn    : RV → RC
  _r·_       : RV → RV → RC
  rreinstall : RC
  rlet       : RC → RC → RC
  r↑         : Σₛ → RV → RC → RC
  r↓         : Σₛ → RV → RC → RC
  rpromise   : Σₛ → RC → RC → RC
  rawait     : RV → RC → RC


-- ERASURE OF WELL-TYPED TERMS TO RAW TERMS (FORGETTING TYPES, EFFECTS, AND COERCIONS)

⌊_⌋∈ : {Γ : Ctx} {X : VType} → X ∈ Γ → ℕ
⌊ Hd ⌋∈ = zero
⌊ Tl x ⌋∈ = suc ⌊ x ⌋∈

⌊_⌋v : {Γ : Ctx} {X : VType} → Γ ⊢V⦂ X → RV

⌊_⌋ : {Γ : Ctx} {Δ : RCtx} {C : CType} → Γ ∣ Δ ⊢M⦂ C → RC

⌊ ` x ⌋v = rvar ⌊ x ⌋∈
⌊ `` c ⌋v = rconst c
⌊ ƛ M ⌋v = rƛ ⌊ M ⌋
⌊ ⟨ V ⟩ ⌋v = r⟨ ⌊ V ⌋v ⟩

⌊ return V ⌋ = rreturn ⌊ V ⌋v
⌊ let= M `in N ⌋ = rlet ⌊ M ⌋ ⌊ N ⌋
⌊ V · W ⌋ = ⌊ V ⌋v r· ⌊ W ⌋v
⌊ reinstall ⌋ = rreinstall
⌊ ↑ op p V M ⌋ = r↑ op ⌊ V ⌋v ⌊ M ⌋
⌊ ↓ op V M ⌋ = r↓ op ⌊ V ⌋v ⌊ M ⌋
⌊ promise op ∣ p ↦ M `in N ⌋ = rpromise op ⌊ M ⌋ ⌊ N ⌋
⌊ await V until M ⌋ = rawait ⌊ V ⌋v ⌊ M ⌋
⌊ coerce p q M ⌋ = ⌊ M ⌋


-- AN OCCURRENCE OF reinstall IN A RAW TERM THAT IS NOT INSIDE THE CODE OF A HANDLER,
-- I.E., ONE THAT WOULD REINSTALL THE HANDLER WHOSE CODE THE TERM IS A PART OF

data OccV : RV → Set

data Occ : RC → Set

data OccV where
  rƛ   : {M : RC} → Occ M → OccV (rƛ M)
  r⟨_⟩ : {V : RV} → OccV V → OccV r⟨ V ⟩

data Occ where
  here      : Occ rreinstall
  rreturn   : {V : RV} → OccV V → Occ (rreturn V)
  r·₁       : {V W : RV} → OccV V → Occ (V r· W)
  r·₂       : {V W : RV} → OccV W → Occ (V r· W)
  rlet₁     : {M N : RC} → Occ M → Occ (rlet M N)
  rlet₂     : {M N : RC} → Occ N → Occ (rlet M N)
  r↑₁       : {op : Σₛ} {V : RV} {M : RC} → OccV V → Occ (r↑ op V M)
  r↑₂       : {op : Σₛ} {V : RV} {M : RC} → Occ M → Occ (r↑ op V M)
  r↓₁       : {op : Σₛ} {V : RV} {M : RC} → OccV V → Occ (r↓ op V M)
  r↓₂       : {op : Σₛ} {V : RV} {M : RC} → Occ M → Occ (r↓ op V M)
  rpromise₂ : {op : Σₛ} {M N : RC} → Occ N → Occ (rpromise op M N)
  rawait₁   : {V : RV} {M : RC} → OccV V → Occ (rawait V M)
  rawait₂   : {V : RV} {M : RC} → Occ M → Occ (rawait V M)


-- AN OCCURRENCE OF reinstall IN A MISPLACED POSITION OF HANDLER CODE: SOMEWHERE IN THE RAW TERM
-- (POSSIBLY INSIDE THE CODE OF A HANDLER) THERE IS A ƛ-ABSTRACTION OR THE BODY OF AN ↓
-- WITH AN OCCURRENCE OF reinstall NOT INSIDE ANY FURTHER HANDLER CODE

data MisplacedV : RV → Set

data Misplaced : RC → Set

data MisplacedV where
  rƛ-occ : {M : RC} → Occ M → MisplacedV (rƛ M)
  rƛ     : {M : RC} → Misplaced M → MisplacedV (rƛ M)
  r⟨_⟩   : {V : RV} → MisplacedV V → MisplacedV r⟨ V ⟩

data Misplaced where
  r↓-occ    : {op : Σₛ} {V : RV} {M : RC} → Occ M → Misplaced (r↓ op V M)
  rreturn   : {V : RV} → MisplacedV V → Misplaced (rreturn V)
  r·₁       : {V W : RV} → MisplacedV V → Misplaced (V r· W)
  r·₂       : {V W : RV} → MisplacedV W → Misplaced (V r· W)
  rlet₁     : {M N : RC} → Misplaced M → Misplaced (rlet M N)
  rlet₂     : {M N : RC} → Misplaced N → Misplaced (rlet M N)
  r↑₁       : {op : Σₛ} {V : RV} {M : RC} → MisplacedV V → Misplaced (r↑ op V M)
  r↑₂       : {op : Σₛ} {V : RV} {M : RC} → Misplaced M → Misplaced (r↑ op V M)
  r↓₁       : {op : Σₛ} {V : RV} {M : RC} → MisplacedV V → Misplaced (r↓ op V M)
  r↓₂       : {op : Σₛ} {V : RV} {M : RC} → Misplaced M → Misplaced (r↓ op V M)
  rpromise₁ : {op : Σₛ} {M N : RC} → Misplaced M → Misplaced (rpromise op M N)
  rpromise₂ : {op : Σₛ} {M N : RC} → Misplaced N → Misplaced (rpromise op M N)
  rawait₁   : {V : RV} {M : RC} → MisplacedV V → Misplaced (rawait V M)
  rawait₂   : {V : RV} {M : RC} → Misplaced M → Misplaced (rawait V M)


-- THE ERASURE OF A WELL-TYPED VALUE, OR OF A WELL-TYPED COMPUTATION OUTSIDE OF
-- HANDLER CODE, CONTAINS NO OCCURRENCES OF reinstall OUTSIDE OF HANDLER CODE

occ-v : {Γ : Ctx}
        {X : VType}
        (V : Γ ⊢V⦂ X) →
        ---------------
        ¬ OccV ⌊ V ⌋v

occ-m : {Γ : Ctx}
        {C : CType}
        (M : Γ ⊢M⦂ C) →
        ---------------
        ¬ Occ ⌊ M ⌋

occ-v (ƛ M) (rƛ p) = occ-m M p
occ-v ⟨ V ⟩ r⟨ p ⟩ = occ-v V p

occ-m (return V) (rreturn p) = occ-v V p
occ-m (let= M `in N) (rlet₁ p) = occ-m M p
occ-m (let= M `in N) (rlet₂ p) = occ-m N p
occ-m (V · W) (r·₁ p) = occ-v V p
occ-m (V · W) (r·₂ p) = occ-v W p
occ-m (↑ op q V M) (r↑₁ p) = occ-v V p
occ-m (↑ op q V M) (r↑₂ p) = occ-m M p
occ-m (↓ op V M) (r↓₁ p) = occ-v V p
occ-m (↓ op V M) (r↓₂ p) = occ-m M p
occ-m (promise op ∣ q ↦ M `in N) (rpromise₂ p) = occ-m N p
occ-m (await V until M) (rawait₁ p) = occ-v V p
occ-m (await V until M) (rawait₂ p) = occ-m M p
occ-m (coerce q r M) p = occ-m M p


-- THE ERASURE OF A WELL-TYPED TERM NEVER CONTAINS reinstall IN A MISPLACED POSITION
-- (UNDER A ƛ OR UNDER AN ↓) OF HANDLER CODE

misplaced-v : {Γ : Ctx}
              {X : VType}
              (V : Γ ⊢V⦂ X) →
              -------------------
              ¬ MisplacedV ⌊ V ⌋v

misplaced-m : {Γ : Ctx}
              {Δ : RCtx}
              {C : CType}
              (M : Γ ∣ Δ ⊢M⦂ C) →
              -----------------
              ¬ Misplaced ⌊ M ⌋

misplaced-v (ƛ M) (rƛ-occ p) = occ-m M p
misplaced-v (ƛ M) (rƛ p) = misplaced-m M p
misplaced-v ⟨ V ⟩ r⟨ p ⟩ = misplaced-v V p

misplaced-m (return V) (rreturn p) = misplaced-v V p
misplaced-m (let= M `in N) (rlet₁ p) = misplaced-m M p
misplaced-m (let= M `in N) (rlet₂ p) = misplaced-m N p
misplaced-m (V · W) (r·₁ p) = misplaced-v V p
misplaced-m (V · W) (r·₂ p) = misplaced-v W p
misplaced-m (↑ op q V M) (r↑₁ p) = misplaced-v V p
misplaced-m (↑ op q V M) (r↑₂ p) = misplaced-m M p
misplaced-m (↓ op V M) (r↓-occ p) = occ-m M p
misplaced-m (↓ op V M) (r↓₁ p) = misplaced-v V p
misplaced-m (↓ op V M) (r↓₂ p) = misplaced-m M p
misplaced-m (promise op ∣ q ↦ M `in N) (rpromise₁ p) = misplaced-m M p
misplaced-m (promise op ∣ q ↦ M `in N) (rpromise₂ p) = misplaced-m N p
misplaced-m (await V until M) (rawait₁ p) = misplaced-v V p
misplaced-m (await V until M) (rawait₂ p) = misplaced-m M p
misplaced-m (coerce q r M) p = misplaced-m M p


-- THE FIRST COUNTEREXAMPLE ↓ op (V , promise (op x r ↦ ↓ op (x , r ())) as p in return p)
-- OF THE DESIGN WITH A FIRST-CLASS REINSTALL FUNCTION r, IN WHICH reinstall IS UNDER AN ↓

M₁raw : Σₛ → RV → RC
M₁raw op V =
  r↓ op V (rpromise op (r↓ op (rvar 0) rreinstall) (rreturn (rvar 0)))

M₁raw-misplaced : {op : Σₛ}
                  {V : RV} →
                  ----------------------
                  Misplaced (M₁raw op V)
M₁raw-misplaced = r↓₂ (rpromise₁ (r↓-occ here))


-- THE SECOND COUNTEREXAMPLE ↓ op (V , promise (op x r ↦ return ⟨ fun () ↦ N ⟩) as p in
-- await p until y in y ()), WHERE N = let p = r () in await p until y in y (),
-- IN WHICH reinstall IS UNDER A ƛ, AND WHERE THE TWO ARGUMENTS () ARE RENDERED
-- AS ARBITRARY RAW VALUES U AND U'

M₂raw : Σₛ → RV → RV → RV → RC
M₂raw op V U U' =
  r↓ op V
    (rpromise op
      (rreturn r⟨ rƛ (rlet rreinstall (rawait (rvar 0) (rvar 0 r· U))) ⟩)
      (rawait (rvar 0) (rvar 0 r· U')))

M₂raw-misplaced : {op : Σₛ}
                  {V U U' : RV} →
                  ---------------------------
                  Misplaced (M₂raw op V U U')
M₂raw-misplaced = r↓₂ (rpromise₁ (rreturn r⟨ rƛ-occ (rlet₁ here) ⟩))


-- NEITHER OF THE COUNTEREXAMPLES IS THE ERASURE OF A WELL-TYPED COMPUTATION

M₁-untypable : {Γ : Ctx}
               {Δ : RCtx}
               {C : CType}
               (op : Σₛ)
               (V : RV) →
               --------------------------------------------
               ¬ Σ (Γ ∣ Δ ⊢M⦂ C) (λ M → ⌊ M ⌋ ≡ M₁raw op V)
M₁-untypable op V (M , p) =
  misplaced-m M (subst Misplaced (sym p) M₁raw-misplaced)

M₂-untypable : {Γ : Ctx}
               {Δ : RCtx}
               {C : CType}
               (op : Σₛ)
               (V U U' : RV) →
               -------------------------------------------------
               ¬ Σ (Γ ∣ Δ ⊢M⦂ C) (λ M → ⌊ M ⌋ ≡ M₂raw op V U U')
M₂-untypable op V U U' (M , p) =
  misplaced-m M (subst Misplaced (sym p) M₂raw-misplaced)


-- THE FIRST COUNTEREXAMPLE IS REJECTED BY THE INTRINSICALLY TYPED SYNTAX:
-- reinstall CANNOT APPEAR UNDER AN ↓, WHOSE BODY IS TYPED IN THE EMPTY REINSTALL CONTEXT

{-
M₁ : {Γ : Ctx} {X : VType} →
     Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! op ↓ₑ (∅ₒ , loop op ∅ₒ)
M₁ =
  ↓ op (` Hd)
    (promise op ∣ loop-hit ↦ coerce ⊑ₒ-refl loop-⊑ᵢ (↓ op (` Hd) reinstall) `in
     return (` Hd))

error: [UnequalTerms]
(re _X_38 (_o_39 , _i_40)) != ∅ of type RCtx
when checking that the expression reinstall has type
(Γ ∷ ``` (payload op) ∷ ``` (payload op)) ∣ ∅ ⊢M⦂
(⟨ _X_11 ⟩ ! (_o_34 , _i_35))
-}


-- THE SECOND COUNTEREXAMPLE IS REJECTED BY THE INTRINSICALLY TYPED SYNTAX:
-- reinstall CANNOT APPEAR UNDER A ƛ, WHOSE BODY IS TYPED IN THE EMPTY REINSTALL CONTEXT

{-
M₂ : {Γ : Ctx} {X : VType} →
     Γ ∷ ```(payload op) ⊢M⦂ X ! op ↓ₑ (∅ₒ , loop op ∅ₒ)
M₂ =
  ↓ op (` Hd)
    (promise op ∣ loop-hit ↦
       return ⟨ ƛ (let= reinstall `in await (` Hd) until ((` Hd) · (` Tl (Tl Hd)))) ⟩ `in
     await (` Hd) until ((` Hd) · (` Tl (Tl Hd))))

error: [UnequalTerms]
re _X_33 (_o_34 , _i_35) != ∅ of type RCtx
when checking that the expression reinstall has type
(Γ ∷ ``` (payload op) ∷ ``` (payload op) ∷ _X_26) ∣ ∅ ⊢M⦂
(_X_29 ! (_o_31 , _i_32))
-}


-- THE CLOSEST LEGAL ANALOGUE OF THE FIRST COUNTEREXAMPLE, IN WHICH THE ↓ IS IN A let-BOUND
-- POSITION AND reinstall IS IN TAIL POSITION:
-- ↓ op (x₀ , promise (op x ↦ let _ = ↓ op (x , return x) in reinstall) as p in return p)

M₁'-code : {Γ : Ctx}
           {X : VType}
           (op : Σₛ) →
           ---------------------------------------------------------------------------------------
           Γ ∷ ```(payload op) ∣ re X (reinst-eff op ∅ₒ (loop op ∅ₒ)) ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , loop op ∅ₒ)
M₁'-code op =
  let= coerce ⊑ₒ-refl ∅ᵢ-⊑ᵢ (↓ op (` Hd) (return {o = ∅ₒ} {i = ∅ᵢ} (` Hd))) `in
  coerce ⊑ₒ-refl loop-⊑ᵢ reinstall

M₁' : {Γ : Ctx}
      {X : VType}
      (op : Σₛ) →
      ---------------------------------------------------------
      Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! op ↓ₑ (∅ₒ , loop op ∅ₒ)
M₁' op =
  ↓ op (` Hd) (promise op ∣ loop-hit ↦ M₁'-code op `in return {o = ∅ₒ} {i = loop op ∅ₒ} (` Hd))


-- THE LEGAL ANALOGUE OF THE FIRST COUNTEREXAMPLE REDUCES TO A NORMAL FORM
-- IN WHICH THE HANDLER HAS BEEN REINSTALLED

M₁'-run : {Γ : Ctx}
          {X : VType}
          (op : Σₛ) →
          ------------------------------------------------------------------
          Σ _ (λ p →
            M₁' {Γ} {X} op ↝* promise op ∣ p ↦ M₁'-code op `in return (` Hd))
M₁'-run op =
  _ ,
  ↓-promise-op _ _ _ _ ∷*
  context (let= coerce _ _ (let= coerce _ _ [-] `in _) `in _) (↓-return _ _) ∷*
  context (let= coerce _ _ (let= [-] `in _) `in _) (coerce-return _) ∷*
  context (let= coerce _ _ [-] `in _) (let-return _ _) ∷*
  context (let= coerce _ _ [-] `in _) (coerce-promise _ _ _) ∷*
  context (let= [-] `in _) (coerce-promise _ _ _) ∷*
  let-promise _ _ _ _ ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= [-] `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (↓-return _ _) ∷*
  []*

M₁'-normal : {Γ : Ctx}
             {X : VType}
             {o : O}
             {i : I}
             {p : _}
             {M : Γ ∷ ```(payload op) ⊢M⦂ ⟨ X ⟩ ! (o , i)} →
             -----------------------------------------------------------------
             ¬ (promise op ∣ p ↦ M₁'-code op `in return {o = o} {i = i} (` Hd) ↝ M)
M₁'-normal r with ↝-to-↝↝ r
... | context-promise ()


-- THE CLOSEST LEGAL ANALOGUE OF THE SECOND COUNTEREXAMPLE, IN WHICH THE RETURNED ƛ
-- DOES NOT REINSTALL THE HANDLER:
-- ↓ op (x₀ , promise (op x ↦ return ⟨ fun z ↦ return z ⟩) as p in await p until y in y x₀)

F : Σₛ → VType
F op = ```(payload op) ⇒ (```(payload op) ! reinst-eff op ∅ₒ ∅ᵢ)

M₂'-code : {Γ : Ctx}
           (op : Σₛ) →
           ----------------------------------------------------------------------------------
           Γ ∷ ```(payload op) ∣ re (F op) (reinst-eff op ∅ₒ ∅ᵢ) ⊢M⦂ ⟨ F op ⟩ ! (∅ₒ , ∅ᵢ)
M₂'-code op =
  return ⟨ ƛ (return (` Hd)) ⟩

M₂' : {Γ : Ctx}
      (op : Σₛ) →
      -----------------------------------------------------------------------
      Γ ∷ ```(payload op) ⊢M⦂ ```(payload op) ! op ↓ₑ (reinst-eff op ∅ₒ ∅ᵢ)
M₂' op =
  ↓ op (` Hd)
    (promise op ∣ reinst-⊑ ↦ M₂'-code op `in
     await_until_ {C = ```(payload op) ! reinst-eff op ∅ₒ ∅ᵢ} (` Hd) ((` Hd) · (` Tl (Tl Hd))))


-- THE LEGAL ANALOGUE OF THE SECOND COUNTEREXAMPLE REDUCES TO A NORMAL FORM

M₂'-run : {Γ : Ctx}
          (op : Σₛ) →
          ----------------------------------
          M₂' {Γ} op ↝* return (` Hd)
M₂'-run op =
  ↓-promise-op _ _ _ _ ∷*
  context (let= [-] `in _) (coerce-return _) ∷*
  let-return _ _ ∷*
  ↓-await _ _ _ ∷*
  await-promise _ _ ∷*
  context (↓ _ _ [-]) (apply _ _) ∷*
  ↓-return _ _ ∷*
  []*

M₂'-normal : {Γ : Ctx}
             {X : VType}
             {o : O}
             {i : I}
             {V : Γ ⊢V⦂ X}
             {M : Γ ⊢M⦂ X ! (o , i)} →
             -------------------------
             ¬ (return V ↝ M)
M₂'-normal r with ↝-to-↝↝ r
... | ()

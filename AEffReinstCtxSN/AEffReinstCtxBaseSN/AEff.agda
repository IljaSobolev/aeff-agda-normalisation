{-# OPTIONS --guardedness #-}

open import Data.List using (List; []) renaming (_∷_ to _∷ₗ_)

open import AEffReinstSN.CoinductiveEffectAnnotations using (Σₛ)
open import AEffReinstCtxSN.AEff using (payload; Σ-base; ar-base)
open import AEffReinstCtxSN.Types using (BType; GType)

open import Relation.Binary.PropositionalEquality using (_≢_)

module AEffReinstCtxSN.AEffReinstCtxBaseSN.AEff where

variable
  A : BType
  op op' : Σₛ

-- VALUE AND COMPUTATION TYPES

infix 30 _⇒_

data Type : Set where
  ``` : GType → Type
  _⇒_ : Type → Type → Type
  ⟨_⟩ : Type → Type

variable
  X Y Z U : Type

-- REINSTALL CONTEXTS: ∅ OUTSIDE OF REINSTALLABLE HANDLER CODE,
-- re X INSIDE THE CODE OF A HANDLER WHOSE PROMISE TYPE IS ⟨ X ⟩

data RCtx : Set where
  ∅  : RCtx
  re : Type → RCtx

variable
  Δ Δ' : RCtx

-- SNOC LISTS FOR MODELLING CONTEXTS

infixl 30 _∷_

data SnocList (A : Set) : Set where
  []  : SnocList A
  _∷_ : SnocList A → A → SnocList A

-- CONTEXTS AND VARIABLES IN THEM (I.E., DE BRUIJN INDICES)

Ctx = SnocList Type

variable
  Γ Γ' Γ'' : Ctx

data _∈_ (X : Type) : Ctx → Set where
  Hd : X ∈ (Γ ∷ X)
  Tl : X ∈ Γ → X ∈ (Γ ∷ Y)


-- DERIVATIONS OF WELL-TYPED TERMS

data _⊢V⦂_ (Γ : Ctx) : Type → Set

data _∣_⊢M⦂_ (Γ : Ctx) : RCtx → Type → Set

data _⊢V⦂_ Γ where
  `_  : X ∈ Γ → Γ ⊢V⦂ X
  ``_ : (c : Σ-base) → Γ ⊢V⦂ ```(ar-base c)
  ƛ   : Γ ∷ X ∣ ∅ ⊢M⦂ Y → Γ ⊢V⦂ X ⇒ Y
  ⟨_⟩ : Γ ⊢V⦂ X → Γ ⊢V⦂ ⟨ X ⟩

infix 40 _·_
data _∣_⊢M⦂_ Γ where

  return         : Γ ⊢V⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  _·_            : Γ ⊢V⦂ X ⇒ Y →
                   Γ ⊢V⦂ X →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  reinstall      : -------
                   Γ ∣ re X ⊢M⦂ ⟨ X ⟩

  let=_`in_      : Γ ∣ ∅ ⊢M⦂ X →
                   Γ ∷ X ∣ Δ ⊢M⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  ↑              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ∣ Δ ⊢M⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  ↓              : (op : Σₛ) →
                   Γ ⊢V⦂ ```(payload op) →
                   Γ ∣ ∅ ⊢M⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  promise_↦_`in_ : (op : Σₛ) →
                   Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩ →
                   Γ ∷ ⟨ X ⟩ ∣ Δ ⊢M⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

  await_until_   : Γ ⊢V⦂ ⟨ X ⟩ →
                   Γ ∷ X ∣ Δ ⊢M⦂ Y →
                   -------
                   Γ ∣ Δ ⊢M⦂ Y

-- COMPUTATIONS OUTSIDE OF HANDLER CODE

_⊢M⦂_ : Ctx → Type → Set
Γ ⊢M⦂ X = Γ ∣ ∅ ⊢M⦂ X

variable
  V V' W W' : Γ ⊢V⦂ X
  M M' N N' L L' : Γ ∣ Δ ⊢M⦂ X


-- SET OF RENAMINGS BETWEEN CONTEXTS

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : Type} → X ∈ Γ → X ∈ Γ'

variable
  r r' : Ren Γ Γ'

-- IDENTITY, COMPOSITION, AND EXCHANGE RENAMINGS

id-ren : Ren Γ Γ
id-ren {X} x = x

-- WEAKENING OF RENAMINGS

wk₁ : Ren Γ (Γ ∷ X)
wk₁ = Tl

wk₂ : Ren Γ Γ' → Ren (Γ ∷ X) (Γ' ∷ X)
wk₂ f Hd = Hd
wk₂ f (Tl v) = Tl (f v)

-- ACTION OF RENAMING ON WELL-TYPED VALUES AND COMPUTATIONS

V-rename : Ren Γ Γ' → Γ ⊢V⦂ X → Γ' ⊢V⦂ X

M-rename : Ren Γ Γ' → Γ ∣ Δ ⊢M⦂ X → Γ' ∣ Δ ⊢M⦂ X

V-rename f (` x) =
  ` f x
V-rename f (`` c) =
  `` c
V-rename f (ƛ M) =
  ƛ (M-rename (wk₂ f) M)
V-rename f ⟨ V ⟩ =
  ⟨ V-rename f V ⟩

M-rename f (return V) =
  return (V-rename f V)
M-rename f (V · W) =
  V-rename f V · V-rename f W
M-rename f reinstall =
  reinstall
M-rename f (let= M `in N) =
  let= M-rename f M `in M-rename (wk₂ f) N
M-rename f (↑ op V M) =
  ↑ op (V-rename f V) (M-rename f M)
M-rename f (↓ op V M) =
  ↓ op (V-rename f V) (M-rename f M)
M-rename f (promise op ↦ M `in N) =
  promise op ↦ M-rename (wk₂ f) M `in M-rename (wk₂ f) N
M-rename f (await V until M) =
  await (V-rename f V) until (M-rename (wk₂ f) M)


-- SET OF SUBSTITUTIONS BETWEEN CONTEXTS

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : Type} → X ∈ Γ → Γ' ⊢V⦂ X

variable
  s s' : Sub Γ Γ'

-- IDENTITY AND EXTENSION SUBSTITUTIONS

id-subst : Sub Γ Γ
id-subst x = ` x

_[_]s : Sub Γ Γ' → Γ' ⊢V⦂ X → Sub (Γ ∷ X) Γ'
(s [ V ]s) Hd = V
(s [ V ]s) (Tl x) = s x

-- LIFTING SUBSTITUTIONS

lift : Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
lift s Hd = ` Hd
lift s (Tl x) = V-rename Tl (s x)

-- ACTION OF SUBSTITUTION ON WELL-TYPED VALUES AND COMPUTATIONS

infix 40 _[_]v
infix 40 _[_]m

_[_]v : Γ ⊢V⦂ X → Sub Γ Γ' → Γ' ⊢V⦂ X

_[_]m : Γ ∣ Δ ⊢M⦂ X → Sub Γ Γ' → Γ' ∣ Δ ⊢M⦂ X

(` x) [ s ]v =
  s x
(`` c) [ s ]v =
  `` c
(ƛ M) [ s ]v =
  ƛ (M [ lift s ]m)
⟨ V ⟩ [ s ]v =
  ⟨ V [ s ]v ⟩

(return V) [ s ]m =
  return (V [ s ]v)
(V · W) [ s ]m =
  (V [ s ]v) · (W [ s ]v)
reinstall [ s ]m =
  reinstall
(let= M `in N) [ s ]m =
  let= M [ s ]m `in N [ lift s ]m
(↑ op V M) [ s ]m =
  ↑ op (V [ s ]v) (M [ s ]m)
(↓ op V M) [ s ]m =
  ↓ op (V [ s ]v) (M [ s ]m)
(promise op ↦ M `in N) [ s ]m =
  promise op ↦ M [ lift s ]m `in (N [ lift s ]m)
(await V until M) [ s ]m =
  await (V [ s ]v) until (M [ lift s ]m)


-- REINSTALL SUBSTITUTION: REPLACING THE FREE OCCURRENCES OF reinstall
-- (THOSE NOT INSIDE NESTED HANDLER CODE) BY A COMPUTATION R

infix 40 _[_]r

_[_]r : Γ ∣ re X ⊢M⦂ Y → Γ ⊢M⦂ ⟨ X ⟩ → Γ ⊢M⦂ Y

(return V) [ R ]r =
  return V
(V · W) [ R ]r =
  V · W
reinstall [ R ]r =
  R
(let= M `in N) [ R ]r =
  let= M `in (N [ M-rename wk₁ R ]r)
(↑ op V M) [ R ]r =
  ↑ op V (M [ R ]r)
(↓ op V M) [ R ]r =
  ↓ op V M
(promise op ↦ M `in N) [ R ]r =
  promise op ↦ M `in (N [ M-rename wk₁ R ]r)
(await V until M) [ R ]r =
  await V until (M [ M-rename wk₁ R ]r)


-- STRENGTHENING OF GROUND VALUES WRT BOUND PROMISES

strengthen-val : Γ ∷ ⟨ X ⟩ ⊢V⦂ ``` A → Γ ⊢V⦂ ``` A
strengthen-val (` Tl x) = ` x
strengthen-val (`` c) = `` c


-- SMALL-STEP OPERATIONAL SEMANTICS FOR WELL-TYPED COMPUTATIONS
-- (OUTSIDE OF HANDLER CODE) WITH INLINED EVALUATION CONTEXT RULES

infix 10 _↝↝_
data _↝↝_ : Γ ⊢M⦂ Y → Γ ⊢M⦂ Y → Set where

  -- COMPUTATIONAL RULES

  apply           : (M : Γ ∷ X ⊢M⦂ Y)
                    (V : Γ ⊢V⦂ X) →
                    ------------
                    ƛ M · V
                    ↝↝
                    M [ id-subst [ V ]s ]m

  let-return      : (V : Γ ⊢V⦂ X)
                    (N : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    let= return V `in N
                    ↝↝
                    N [ id-subst [ V ]s ]m

  let-↑           : (N : Γ ∷ X ⊢M⦂ Y)
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    ------------
                    let= ↑ op V M `in N
                    ↝↝
                    ↑ op V (let= M `in N)

  ↓-↑             : (V' : Γ ⊢V⦂ ```(payload op'))
                    (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ⊢M⦂ X) →
                    -------------------
                    ↓ op' V' (↑ op V M)
                    ↝↝
                    ↑ op V (↓ op' V' M)

  let-promise     : (L : Γ ∷ Z ⊢M⦂ Y)
                    (M : Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Z) →
                    --------------------------
                    let= promise op ↦ M `in N `in L
                    ↝↝
                    promise op ↦ M `in (let= N `in M-rename (wk₂ wk₁) L)

  let-await       : (N : Γ ∷ Y ⊢M⦂ Z)
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    let= await V until M `in N
                    ↝↝
                    await V until let= M `in M-rename (wk₂ wk₁) N

  ↓-await         : (W : Γ ⊢V⦂ ```(payload op))
                    (V : Γ ⊢V⦂ ⟨ X ⟩)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    ↓ op W (await V until M)
                    ↝↝
                    await V until ↓ op (V-rename wk₁ W) M

  promise-↑       : (V : Γ ∷ ⟨ X ⟩ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    --------------------
                    promise op ↦ M `in (↑ op' V N)
                    ↝↝
                    ↑ op' (strengthen-val V) (promise op ↦ M `in N)

  ↓-return        : (V : Γ ⊢V⦂ ```(payload op))
                    (W : Γ ⊢V⦂ Y) →
                    ------------
                    ↓ op V (return W)
                    ↝↝
                    return W

  ↓-promise-op    : (V : Γ ⊢V⦂ ```(payload op))
                    (M : Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    -----------------------------
                    ↓ op V (promise op ↦ M `in N)
                    ↝↝
                    let=
                      (M [ id-subst [ V ]s ]m) [ promise op ↦ M `in return (` Hd) ]r `in
                      ↓ op (V-rename wk₁ V) N

  ↓-promise-op'   : (p : op ≢ op')
                    (V : Γ ⊢V⦂ ```(payload op'))
                    (M : Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩)
                    (N : Γ ∷ ⟨ X ⟩ ⊢M⦂ Y) →
                    -------------------------------
                    ↓ op' V (promise op ↦ M `in N)
                    ↝↝
                    promise op ↦ M `in ↓ op' (V-rename wk₁ V) N

  await-promise   : (V : Γ ⊢V⦂ X)
                    (M : Γ ∷ X ⊢M⦂ Y) →
                    ----------------
                    await ⟨ V ⟩ until M
                    ↝↝
                    M [ id-subst [ V ]s ]m

  -- INLINED EVALUATION CONTEXT RULES

  context-↑       : N ↝↝ N' →
                    -----
                    ↑ op V N
                    ↝↝
                    ↑ op V N'

  context-promise : {M : Γ ∷ ```(payload op) ∣ re X ⊢M⦂ ⟨ X ⟩} →
                    N ↝↝ N' →
                    -----
                    promise op ↦ M `in N
                    ↝↝
                    promise op ↦ M `in N'

  context-let     : M ↝↝ M' →
                    -----
                    let= M `in N
                    ↝↝
                    let= M' `in N

  context-↓       : M ↝↝ M' →
                    -----
                    ↓ op V M
                    ↝↝
                    ↓ op V M'

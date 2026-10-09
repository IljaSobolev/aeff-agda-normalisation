{-# OPTIONS --guardedness #-}

open import Data.Maybe using (just)
open import Data.Product using (_,_; Σ-syntax)

open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Relation.Nullary using (¬_)

open import AEffReinstSN.CoinductiveEffectAnnotations
open import AEffReinstCtxSN.Types
open import AEffReinstCtxSN.AEff
open import AEffReinstCtxSN.Renamings
open import AEffReinstCtxSN.Substitutions
open import AEffReinstCtxSN.Preservation
open import AEffReinstCtxSN.ExamplePreliminaries
open import AEffReinstCtxSN.Finality using (_↝↝_; ↝-to-↝↝; context-↑; context-promise)

module AEffReinstCtxSN.Examples
  (request response stop go : Σₛ)
  (stop≢go : stop ≢ go)
  where

-- THE ANNOTATIONS OF THE EXAMPLES BELOW

i-server : I
i-server = loop request [ response ]ₒ

i-thread : I
i-thread = two stop ∅ₒ go (just (∅ₒ , ∅ᵢ))

i-inner : I
i-inner = loop go ∅ₒ

i-nested : I
i-nested = two stop ∅ₒ go (just (∅ₒ , i-inner))


-- A SERVER: promise (request x ↦ let y = return w in ↑ response y reinstall) as p in return p,
-- WHERE THE VARIABLE w HOLDS THE RESPONSE PAYLOAD, AND WITH EFFECT ANNOTATION
-- i-server = { request ↦ ({ response } , i-server) }

server-code : {Γ : Ctx}
              {X : VType} →
              ```(payload response) ∈ Γ →
              ---------------------------------------------------------------------------------------------
              Γ ∷ ```(payload request) ∣ re X (reinst-eff request [ response ]ₒ i-server) ⊢M⦂ ⟨ X ⟩ ! ([ response ]ₒ , i-server)
server-code w =
  let= return (` Tl w) `in
  ↑ response ∈-[]ₒ (` Hd) (coerce ∅ₒ-⊑ₒ loop-⊑ᵢ reinstall)

server : {Γ : Ctx}
         {X : VType} →
         ```(payload response) ∈ Γ →
         ----------------------------------------------
         Γ ⊢M⦂ ⟨ X ⟩ ! ([ response ]ₒ , i-server)
server w =
  promise request ∣ loop-hit ↦ server-code w `in return (` Hd)


-- PRE-EMPTIVE THREADS: promise (stop x ↦ promise (go y ↦ return ⟨ x ⟩) as p in
-- await p until z in reinstall) as q in return q, WHERE THE CODE OF THE go-HANDLER
-- FINISHES AND THE reinstall IN ITS CONTINUATION REINSTALLS THE stop-HANDLER

thread-code : {Γ : Ctx}
              {X : VType} →
              -------------------------------------------------------------------------------
              Γ ∷ ```(payload stop) ∣ re X (reinst-eff stop ∅ₒ i-thread) ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-thread)
thread-code =
  promise go ∣ two-hit' stop≢go ↦ return ⟨ ` Tl Hd ⟩ `in
  await ` Hd until
  coerce ⊑ₒ-refl two-⊑ᵢ reinstall

thread : {Γ : Ctx}
         {X : VType} →
         ------------------------------
         Γ ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-thread)
thread =
  promise stop ∣ two-hit ↦ thread-code `in return (` Hd)


-- NESTED SCOPING: promise (stop x ↦ promise (go y ↦ reinstall) as p in reinstall) as q in return q,
-- WHERE THE reinstall IN THE CODE OF THE go-HANDLER REINSTALLS THE go-HANDLER (OF TYPE ⟨ payload go ⟩)
-- AND THE reinstall IN ITS CONTINUATION REINSTALLS THE stop-HANDLER (OF TYPE ⟨ X ⟩)

inner-code : {Γ : Ctx} →
             ------------------------------------------------------------------------------------------------------
             Γ ∷ ```(payload go) ∣ re (```(payload go)) (reinst-eff go ∅ₒ i-inner) ⊢M⦂ ⟨ ```(payload go) ⟩ ! (∅ₒ , i-inner)
inner-code =
  coerce ⊑ₒ-refl loop-⊑ᵢ reinstall

nested-code : {Γ : Ctx}
              {X : VType} →
              -------------------------------------------------------------------------------
              Γ ∷ ```(payload stop) ∣ re X (reinst-eff stop ∅ₒ i-nested) ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-nested)
nested-code =
  promise go ∣ two-hit' stop≢go ↦ inner-code `in
  coerce ⊑ₒ-refl two-⊑ᵢ reinstall

nested : {Γ : Ctx}
         {X : VType} →
         ------------------------------
         Γ ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-nested)
nested =
  promise stop ∣ two-hit ↦ nested-code `in return (` Hd)



-- THE SERVER UNDER TWO INCOMING REQUESTS ISSUES TWO RESPONSES
-- AND ENDS UP WITH ITS HANDLER REINSTALLED AND WAITING FOR THE NEXT REQUEST

server-run : {Γ : Ctx}
             {X : VType}
             (w : ```(payload response) ∈ Γ)
             (V₁ V₂ : Γ ⊢V⦂ ```(payload request)) →
             ------------------------------------------------------------------------------
             Σ[ r₁ ∈ _ ] Σ[ r₂ ∈ _ ] Σ[ p ∈ _ ]
               (↓ request V₁ (↓ request V₂ (server {X = X} w))
                ↝*
                ↑ response r₁ (` w) (↑ response r₂ (` w)
                  (promise request ∣ p ↦ server-code w `in return (` Hd))))
server-run w V₁ V₂ =
  _ , _ , _ ,
  context (↓ _ _ [-]) (↓-promise-op _ _ _ _) ∷*
  context (↓ _ _ (let= coerce _ _ [-] `in _)) (let-return _ _) ∷*
  context (↓ _ _ (let= [-] `in _)) (coerce-↑ _ _ _) ∷*
  context (↓ _ _ [-]) (let-↑ _ _ _ _) ∷*
  ↓-↑ _ _ _ _ ∷*
  context (↑ _ _ _ (↓ _ _ (let= coerce _ _ [-] `in _))) (coerce-promise _ _ _) ∷*
  context (↑ _ _ _ (↓ _ _ (let= [-] `in _))) (coerce-promise _ _ _) ∷*
  context (↑ _ _ _ (↓ _ _ [-])) (let-promise _ _ _ _) ∷*
  context (↑ _ _ _ [-]) (↓-promise-op _ _ _ _) ∷*
  context (↑ _ _ _ (let= coerce _ _ [-] `in _)) (let-return _ _) ∷*
  context (↑ _ _ _ (let= [-] `in _)) (coerce-↑ _ _ _) ∷*
  context (↑ _ _ _ [-]) (let-↑ _ _ _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (let= coerce _ _ [-] `in _))) (coerce-promise _ _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (let= [-] `in _))) (coerce-promise _ _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ [-])) (let-promise _ _ _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)))) (coerce-return _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (let= [-] `in _)))) (coerce-return _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in [-]))) (let-return _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ [-] `in _))))) (coerce-return _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= [-] `in _))))) (coerce-return _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ [-])))) (let-return _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ [-])))) (↓-return _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in [-]))) (↓-return _ _) ∷*
  []*


-- THE RESULT OF THE SERVER RUN IS IN NORMAL FORM

server-final-normal : {Γ : Ctx}
                      {X : VType}
                      {o : O}
                      {i' : I}
                      {p : _}
                      {r₁ : response ∈ₒ o}
                      {r₂ : response ∈ₒ o}
                      {M : Γ ⊢M⦂ ⟨ X ⟩ ! (o , i')}
                      (w : ```(payload response) ∈ Γ) →
                      ---------------------------------------------------------------------
                      ¬ (↑ response r₁ (` w) (↑ response r₂ (` w)
                          (promise request ∣ p ↦ server-code w `in return {i = i'} (` Hd))) ↝ M)
server-final-normal w r with ↝-to-↝↝ r
... | context-↑ (context-↑ (context-promise ()))


-- IN THE NESTED EXAMPLE, A stop INTERRUPT REPLACES ONLY THE reinstall IN THE CONTINUATION
-- OF THE go-HANDLER BY THE stop-HANDLER, WHILE THE reinstall IN THE CODE OF THE go-HANDLER
-- IS LEFT UNTOUCHED (IT WILL REINSTALL THE go-HANDLER)

nested-after-stop : {Γ : Ctx}
                    {X : VType} →
                    -----------------------------
                    Γ ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-nested)
nested-after-stop =
  promise go ∣ two-hit' stop≢go ↦ inner-code `in
  coerce ⊑ₒ-refl two-⊑ᵢ (reinst-handler nested-code)

nested-stop : {Γ : Ctx}
              {X : VType}
              (V : Γ ⊢V⦂ ```(payload stop)) →
              ------------------------------------------------------------------------
              ↓ stop V (nested {X = X})
              ↝
              let= coerce (o⊑ {i = i-nested} two-hit) (i⊑ {i = i-nested} {o = ∅ₒ} two-hit) nested-after-stop `in
              ↓ stop (V-rename wk₁ V) (return {o = ∅ₒ} {i = i-nested} (` Hd))
nested-stop V =
  ↓-promise-op _ _ _ _


-- A SUBSEQUENT go INTERRUPT IS HANDLED BY THE go-HANDLER, WHOSE reinstall REINSTALLS
-- THE go-HANDLER, SO THAT IN THE END BOTH HANDLERS ARE INSTALLED AND WAITING

nested-run : {Γ : Ctx}
             {X : VType}
             (V : Γ ⊢V⦂ ```(payload stop))
             (W : Γ ⊢V⦂ ```(payload go)) →
             ------------------------------------------------------------------------
             Σ[ p ∈ _ ] Σ[ q ∈ _ ]
               (↓ go W (↓ stop V (nested {X = X}))
                ↝*
                promise go ∣ p ↦ inner-code `in
                promise stop ∣ q ↦ nested-code `in
                return (` Hd))
nested-run V W =
  _ , _ ,
  context (↓ _ _ [-]) (↓-promise-op _ _ _ _) ∷*
  context (↓ _ _ (let= [-] `in _)) (coerce-promise _ _ _) ∷*
  context (↓ _ _ [-]) (let-promise _ _ _ _) ∷*
  ↓-promise-op _ _ _ _ ∷*
  context (let= coerce _ _ [-] `in _) (coerce-promise _ _ _) ∷*
  context (let= [-] `in _) (coerce-promise _ _ _) ∷*
  let-promise _ _ _ _ ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= [-] `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ [-] `in _))) (coerce-promise _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= [-] `in _))) (coerce-promise _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (↓ _ _ [-])) (let-promise _ _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (↓-promise-op' (λ e → stop≢go (sym e)) _ _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ [-] `in _)))) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= [-] `in _)))) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (↓ _ _ [-]))) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (↓ _ _ [-]))) (↓-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in [-])) (↓-return _ _) ∷*
  []*


-- AN EARLY-REINSTALL SERVER: promise (request x ↦ let q = reinstall in let y = return w in
-- ↑ response y (return q)) as p in return p, WHOSE CODE REINSTALLS THE HANDLER IN A let-BOUND
-- POSITION BEFORE ISSUING THE RESPONSE, AND RETURNS THE PROMISE OF THE REINSTALLED HANDLER

early-code : {Γ : Ctx}
             {X : VType} →
             ```(payload response) ∈ Γ →
             ---------------------------------------------------------------------------------------------
             Γ ∷ ```(payload request) ∣ re X (reinst-eff request [ response ]ₒ i-server) ⊢M⦂ ⟨ X ⟩ ! ([ response ]ₒ , i-server)
early-code w =
  let= coerce ∅ₒ-⊑ₒ loop-⊑ᵢ reinstall `in
  let= return (` Tl (Tl w)) `in
  ↑ response ∈-[]ₒ (` Hd) (return (` Tl Hd))

early-server : {Γ : Ctx}
               {X : VType} →
               ```(payload response) ∈ Γ →
               ----------------------------------------------
               Γ ⊢M⦂ ⟨ X ⟩ ! ([ response ]ₒ , i-server)
early-server w =
  promise request ∣ loop-hit ↦ early-code w `in return (` Hd)


-- AFTER A request INTERRUPT, THE REINSTALLED HANDLER FLOATS OUT BEFORE THE RESPONSE IS ISSUED,
-- SO THAT A SECOND request INTERRUPT IS HANDLED BY IT WHILE THE FIRST RESPONSE IS STILL PENDING IN N

early-run : {Γ : Ctx}
            {X : VType}
            (w : ```(payload response) ∈ Γ)
            (V₁ V₂ : Γ ⊢V⦂ ```(payload request)) →
            ------------------------------------------------------------------------------------------
            Σ[ p ∈ _ ] Σ[ q ∈ _ ] Σ[ N ∈ Γ ∷ ⟨ X ⟩ ⊢M⦂ ⟨ X ⟩ ! (request ↓ₑ ([ response ]ₒ , i-server)) ]
              (↓ request V₁ (↓ request V₂ (early-server {X = X} w))
               ↝*
               let= coerce p q ((early-code w [ id-subst [ V₁ ]s ]m) [ reinst-handler (early-code w) ]r) `in
               ↓ request (V-rename wk₁ V₁) N)
early-run w V₁ V₂ =
  _ , _ , _ ,
  context (↓ _ _ [-]) (↓-promise-op _ _ _ _) ∷*
  context (↓ _ _ (let= coerce _ _ (let= [-] `in _) `in _)) (coerce-promise _ _ _) ∷*
  context (↓ _ _ (let= coerce _ _ [-] `in _)) (let-promise _ _ _ _) ∷*
  context (↓ _ _ (let= [-] `in _)) (coerce-promise _ _ _) ∷*
  context (↓ _ _ [-]) (let-promise _ _ _ _) ∷*
  ↓-promise-op _ _ _ _ ∷*
  []*


-- RUNNING THE EARLY-REINSTALL SERVER UNDER TWO INCOMING REQUESTS TO THE END ISSUES TWO RESPONSES
-- AND LEAVES THE HANDLER REINSTALLED BY THE SECOND REQUEST WAITING FOR THE NEXT ONE

early-run-final : {Γ : Ctx}
                  {X : VType}
                  (w : ```(payload response) ∈ Γ)
                  (V₁ V₂ : Γ ⊢V⦂ ```(payload request)) →
                  ------------------------------------------------------------------------------
                  Σ[ r₁ ∈ _ ] Σ[ r₂ ∈ _ ] Σ[ p ∈ _ ]
                    (↓ request V₁ (↓ request V₂ (early-server {X = X} w))
                     ↝*
                     ↑ response r₁ (` w) (↑ response r₂ (` w)
                       (promise request ∣ p ↦ early-code w `in return (` Hd))))
early-run-final w V₁ V₂ =
  _ , _ , _ ,
  context (↓ _ _ [-]) (↓-promise-op _ _ _ _) ∷*
  context (↓ _ _ (let= coerce _ _ (let= [-] `in _) `in _)) (coerce-promise _ _ _) ∷*
  context (↓ _ _ (let= coerce _ _ [-] `in _)) (let-promise _ _ _ _) ∷*
  context (↓ _ _ (let= [-] `in _)) (coerce-promise _ _ _) ∷*
  context (↓ _ _ [-]) (let-promise _ _ _ _) ∷*
  ↓-promise-op _ _ _ _ ∷*
  context (let= coerce _ _ (let= [-] `in _) `in _) (coerce-promise _ _ _) ∷*
  context (let= coerce _ _ [-] `in _) (let-promise _ _ _ _) ∷*
  context (let= [-] `in _) (coerce-promise _ _ _) ∷*
  let-promise _ _ _ _ ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ (let= [-] `in _) `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= [-] `in _)) (coerce-↑ _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (let-↑ _ _ _ _) ∷*
  promise-↑ _ _ _ _ _ ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (let= [-] `in _))) (coerce-return _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in [-])) (let-return _ _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ (let= [-] `in _) `in _)))) (coerce-return _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ [-] `in _)))) (let-return _ _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= coerce _ _ [-] `in _)))) (let-return _ _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= [-] `in _)))) (coerce-↑ _ _ _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ [-]))) (let-↑ _ _ _ _) ∷*
  context (↑ _ _ _ (promise _ ∣ _ ↦ _ `in [-])) (↓-↑ _ _ _ _) ∷*
  context (↑ _ _ _ [-]) (promise-↑ _ _ _ _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ (let= [-] `in _))))) (coerce-return _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ [-])))) (let-return _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in (↓ _ _ [-])))) (↓-return _ _) ∷*
  context (↑ _ _ _ (↑ _ _ _ (promise _ ∣ _ ↦ _ `in [-]))) (↓-return _ _) ∷*
  []*


-- A DOUBLE REINSTALL: promise (go x ↦ let _ = reinstall in reinstall) as p in return p,
-- WHOSE CODE REINSTALLS THE HANDLER TWICE

double-code : {Γ : Ctx}
              {X : VType} →
              -------------------------------------------------------------------------------
              Γ ∷ ```(payload go) ∣ re X (reinst-eff go ∅ₒ i-inner) ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-inner)
double-code =
  let= coerce ⊑ₒ-refl loop-⊑ᵢ reinstall `in
  coerce ⊑ₒ-refl loop-⊑ᵢ reinstall

double : {Γ : Ctx}
         {X : VType} →
         -----------------------------
         Γ ⊢M⦂ ⟨ X ⟩ ! (∅ₒ , i-inner)
double =
  promise go ∣ loop-hit ↦ double-code `in return (` Hd)


-- AFTER A go INTERRUPT, TWO COPIES OF THE HANDLER ARE INSTALLED AND WAITING

double-run : {Γ : Ctx}
             {X : VType}
             (V : Γ ⊢V⦂ ```(payload go)) →
             ---------------------------------------------------
             Σ[ p ∈ _ ] Σ[ q ∈ _ ]
               (↓ go V (double {X = X})
                ↝*
                promise go ∣ p ↦ double-code `in
                promise go ∣ q ↦ double-code `in
                return (` Hd))
double-run V =
  _ , _ ,
  ↓-promise-op _ _ _ _ ∷*
  context (let= coerce _ _ (let= [-] `in _) `in _) (coerce-promise _ _ _) ∷*
  context (let= coerce _ _ [-] `in _) (let-promise _ _ _ _) ∷*
  context (let= [-] `in _) (coerce-promise _ _ _) ∷*
  let-promise _ _ _ _ ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ (let= [-] `in _) `in _)) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _)) (coerce-promise _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (let= [-] `in _)) (coerce-promise _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in [-]) (let-promise _ _ _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (let= coerce _ _ [-] `in _))) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in (let= [-] `in _))) (coerce-return _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in [-])) (let-return _ _) ∷*
  context (promise _ ∣ _ ↦ _ `in (promise _ ∣ _ ↦ _ `in [-])) (↓-return _ _) ∷*
  []*

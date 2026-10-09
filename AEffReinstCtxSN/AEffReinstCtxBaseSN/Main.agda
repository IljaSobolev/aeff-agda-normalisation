{-# OPTIONS --guardedness #-}

open import AEffReinstCtxSN.AEffReinstCtxBaseSN.AEff
open import AEffReinstCtxSN.AEffReinstCtxBaseSN.StronglyNormalising
open import AEffReinstCtxSN.AEffReinstCtxBaseSN.SubstitutionProperties
open import AEffReinstCtxSN.AEffReinstCtxBaseSN.Continuations

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂) renaming (module ≡-Reasoning to Eq)
open Eq using (begin_; step-≡-⟩; _∎)

open import Function using (_∘_)

module AEffReinstCtxSN.AEffReinstCtxBaseSN.Main where

private variable
  R : Γ ⊢M[ ∅ ]⦂ X


-- DEFINITION OF KRIPKE-STYLE LOGICAL RELATION

VRed : Γ ⊢V⦂ X → Set

CRed : Γ ⊢M[ ∅ ]⦂ X → Set

KRed : Γ ⊢K⦂ X ⊸ Y [ n ] → Set

ARed : Γ ⊢K⦂ Y ⊸ Z [ n ] → Γ ∷ X ⊢M[ ∅ ]⦂ Y → Set

VRed {Γ} {``` _} V =
  ⊤
VRed {Γ} {X ⇒ Y} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {W : Γ' ⊢V⦂ X} → VRed W → CRed (V-rename r V · W)
VRed {Γ} {⟨ X ⟩} V =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y Z : Type} {n : ℕ} (K : Γ' ⊢K⦂ Y ⊸ Z [ n ]) (N : Γ' ∷ X ⊢M[ ∅ ]⦂ Y) → ARed K N → SN' (K aₖ await V-rename r V until N)

CRed {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Y : Type} {n : ℕ} (K : Γ' ⊢K⦂ X ⊸ Y [ n ]) → KRed K → SN' (K aₖ M-rename r M)

KRed {Γ} {X} K =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ return V)

ARed {Γ} {Y} {Z} {n} {X} K N =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → SN' (K-rename r K aₖ await ⟨ V ⟩ until M-rename (wk₂ r) N)


-- REDUCIBILITY OF COMPUTATIONS IN REINSTALL CONTEXT re X (I.E., OF HANDLER CODE):
-- reinstall BEHAVES LIKE A SECOND-CLASS JUMP TO R, WHICH IS ONLY REQUIRED TO BE
-- STRONGLY NORMALISING UNDER THE CONTINUATION K

CRedR : Γ ⊢M[ re X ]⦂ ⟨ X ⟩ → Set
CRedR {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {Z : Type} {n : ℕ} (K : Γ' ⊢K⦂ ⟨ X ⟩ ⊸ Z [ n ]) → KRed K →
  (R : Γ' ⊢M[ ∅ ]⦂ ⟨ X ⟩) → SN (K aₖ R) → SN' (K aₖ M-rename r M [ R ]r)


-- AUXILIARY PREDICATES EXPRESSING THAT ALL ONE-VARIABLE SUBSTITUTIONS OF
-- REDUCIBLE COMPUTATIONS WITH REDUCIBLE VALUES RESULTS IN REDUCIBLE COMPUTATIONS

CRedSub' : Γ ∷ X ⊢M[ ∅ ]⦂ Y → Set
CRedSub' {Γ} {X} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ X} → VRed V → CRed (M-rename (wk₂ r) M [ id-subst [ V ]s ]m)

CRedSubR' : Γ ∷ Y ⊢M[ re X ]⦂ ⟨ X ⟩ → Set
CRedSubR' {Γ = Γ} {Y = Y} M =
  {Γ' : Ctx} {r : Ren Γ Γ'} {V : Γ' ⊢V⦂ Y} → VRed V → CRedR (M-rename (wk₂ r) M [ id-subst [ V ]s ]m)


-- THE LOGICAL RELATION IS PRESERVED UNDER RENAMINGS

vred-r : VRed V → VRed (V-rename r V)
vred-r {_} {``` x} rV = tt
vred-r {_} {X ⇒ Y} rV rW K rK = subst SN' (cong (λ z → K aₖ V-rename _ z · _) (sym ren-ren-v)) (rV rW K rK)
vred-r {_} {⟨ X ⟩} rV K N rA = subst SN' (cong (λ z → K aₖ await z until _) (sym ren-ren-v)) (rV K N rA)

kred-r : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → KRed (K-rename r K)
kred-r K rK rV = subst SN' (cong (_aₖ _) (sym (ren-ren-k K))) (rK rV)

credsub'-r : CRedSub' M → CRedSub' (M-rename (wk₂ r) M)
credsub'-r rM rV K rK = subst (λ z → SN' (K aₖ M-rename _ (z [ id-subst [ _ ]s ]m))) (sym ren-ren-l) (rM rV K rK)

credsubr'-r : CRedSubR' M → CRedSubR' (M-rename (wk₂ r) M)
credsubr'-r rM rV K rK R sR = subst (λ z → SN' (K aₖ M-rename _ (z [ id-subst [ _ ]s ]m) [ R ]r)) (sym ren-ren-l) (rM rV K rK R sR)


-- STRONG NORMALISATION OF A CONTINUATION APPLIED TO A COMPUTATION IS PRESERVED UNDER RENAMINGS

sn-ren-aₖ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ M) → SN (K-rename r K aₖ M-rename r M)
sn-ren-aₖ K s = subst SN (ren-aₖ K) (ren-sn s)


-- REDUCIBLE CONTINUATIONS APPLIED TO REDUCIBLE COMPUTATIONS RESULT IN STRONGLY NORMALISING TERMS

cred-kred : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRed M → SN' (K aₖ M)
cred-kred K rK rM = subst (λ z → SN' (K aₖ z)) ren-id-m (rM K rK)

credr-kred : (K : Γ ⊢K⦂ ⟨ X ⟩ ⊸ Y [ n ]) → KRed K → CRedR M → SN (K aₖ R) → SN' (K aₖ M [ R ]r)
credr-kred {M = M} {R = R} K rK rM sR = subst (λ z → SN' (K aₖ z [ R ]r)) (ren-id-m {M = M}) (rM {r = id-ren} K rK R sR)


-- PROOFS OF THE REDUCIBILITY LEMMAS FOR EACH TERM CONSTRUCTOR

-- VARIABLES ARE REDUCIBLE

sn-var-await : {x : ⟨ X ⟩ ∈ Γ} (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN' (K aₖ await ` x until N)
sn-var-await K r with aₖ→`aₖ K r
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-var-await K)
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-var-await K)

vred-var : (x : X ∈ Γ) → VRed (` x)
vred-var {``` _} _ = tt
vred-var {_ ⇒ _} _ _ K _ r with aₖ→`aₖ K r
... | ↝∘l _ (context-let ())
... | ↝∘↓ _ (context-↓ ())
vred-var {⟨ _ ⟩} _ K _ _ = sn-var-await K


-- CREDSUB IS ALSO PRESERVED UNDER RENAMINGS (USING REDUCIBILITY OF VARIABLES)

credsub'→cred : CRedSub' M → CRed (M-rename (wk₂ r) M)
credsub'→cred rM =
  subst CRed
    (trans (sub-ren-m (λ {Hd → refl; (Tl x) → refl})) (cong (M-rename _) sub-id-m))
    (rM (vred-var Hd))

credsubr'→credr : CRedSubR' M → CRedR (M-rename (wk₂ r) M)
credsubr'→credr rM =
  subst CRedR
    (trans (sub-ren-m (λ {Hd → refl; (Tl x) → refl})) (cong (M-rename _) sub-id-m))
    (rM (vred-var Hd))


-- LAMBDA ABSTRACTIONS ARE REDUCIBLE

sn-ƛ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ M [ id-subst [ W ]s ]m) → SN' (K aₖ ƛ M · W)
sn-ƛ K s r with aₖ→`aₖ K r
... | ↝id (apply _ _) = s
... | ↝∘l _ (context-let (apply _ _)) = s
... | ↝∘↓ _ (context-↓ (apply _ _)) = s

vred-ƛ : CRedSub' M → VRed (ƛ M)
vred-ƛ rM rW K rK = sn-ƛ K (subst (λ z → SN (K aₖ z [ id-subst [ _ ]s ]m)) (sym ren-ren-l) (sn'→sn (cred-kred K rK (rM (vred-r rW)))))


-- LET-TERMS ARE REDUCIBLE

sn-let-return : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ N [ id-subst [ V ]s ]m) → SN' (K aₖ let= return V `in N)
sn-let-return K s r with aₖ→`aₖ K r
... | ↝id (let-return _ _) = s
... | ↝∘l _ (context-let (let-return _ _)) = s
... | ↝∘↓ _ (context-↓ (let-return _ _)) = s

kred-let : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRedSub' N → KRed (K ∘l N)
kred-let K rK rN rV = sn-let-return (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-let : CRed M → CRedSub' N → CRed (let= M `in N)
cred-let rM rN K rK = rM (K ∘l _) (kred-let K rK (credsub'-r rN))


-- INTERRUPTS ARE REDUCIBLE

sn-↓ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ return V) → SN' (K aₖ ↓ op W (return V))
sn-↓ K s r with aₖ→`aₖ K r
... | ↝id (↓-return _ _) = s
... | ↝∘l _ (context-let (↓-return _ _)) = s
... | ↝∘↓ _ (context-↓ (↓-return _ _)) = s

kred-↓ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → KRed (K ∘↓ op [ V ])
kred-↓ K rK rV = sn-↓ (K-rename _ K) (sn'→sn (rK rV))

cred-↓ : CRed M → CRed (↓ op V M)
cred-↓ rM K rK = rM (K ∘↓ _ [ _ ]) (kred-↓ K rK)


-- RETURN IS REDUCIBLE

cred-return : VRed V → CRed (return V)
cred-return rV K rK = subst (λ z → SN' (z aₖ return _)) (ren-id-k K) (rK (vred-r rV))


-- SIGNALS ARE REDUCIBLE

sn-↑ : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → SN (K aₖ M) → SN' (K aₖ ↑ op V M)
sn-↑ K (sn f) r with aₖ→`aₖ K r
... | ↝id (context-↑ r) = sn'→sn (sn-↑ {n = 0} id (f r))
... | ↝∘l K (let-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘l _ (context-let (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))
... | ↝∘↓ K (↓-↑ _ _ _) = sn'→sn (sn-↑ K (sn f))
... | ↝∘↓ _ (context-↓ (context-↑ r)) = sn'→sn (sn-↑ K (f (context-K K r)))

cred-↑ : CRed M → CRed (↑ op V M)
cred-↑ rM K rK = sn-↑ K (sn'→sn (rM K rK))


-- AWAIT-TERMS ARE REDUCIBLE

sn-await : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN (K aₖ N [ id-subst [ V ]s ]m) → SN' (K aₖ await ⟨ V ⟩ until N)
sn-await K s r with aₖ→`aₖ K r
... | ↝id (await-promise _ _) = s
... | ↝∘l K (let-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ let= _ `in z)) (wk₂wk₁M[liftid-subst[W]] _ _) s))
... | ↝∘↓ K (↓-await _ _ _) = sn'→sn (sn-await K (subst (λ z → SN (K aₖ ↓ _ z _)) (wk₁V[id-subst[W]] _ _) s))
... | ↝∘l _ (context-let (await-promise _ _)) = s
... | ↝∘↓ _ (context-↓ (await-promise _ _)) = s

ared-await : (K : Γ ⊢K⦂ X ⊸ Y [ n ]) → KRed K → CRedSub' N → ARed K N
ared-await K rK rN rV = sn-await (K-rename _ K) (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (rN rV)))

cred-await : VRed V → CRedSub' N → CRed (await V until N)
cred-await rV rN K rK = rV K _ (ared-await K rK (credsub'-r rN))


-- PROMISE VALUES ARE REDUCIBLE

vred-⟨⟩ : VRed V → VRed ⟨ V ⟩
vred-⟨⟩ rV K N rK = subst₂ (λ z w → SN' (z aₖ await ⟨ V-rename _ _ ⟩ until w)) (ren-id-k K) ren-id-l (rK (vred-r rV))


-- REMOVING A SIGNAL FROM A COMPUTATIONS KEEPS IT STRONGLY NORMALISING
-- AND DOES NOT INCREASE THE MAXIMUM REDUCTION LENGTH

sn-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → SN (K aₖ ↑ op V M) → SN' (K aₖ M)
sn-k-↑-e K (sn sM) r with aₖ→`aₖ K r
... | ↝id r = sn'→sn (sn-k-↑-e id (sM (context-↑ r)))
... | ↝∘l K r = sn-k-↑-e K (sM (context-K K (let-↑ _ _ _))) (context-K K r)
... | ↝∘↓ K r = sn-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) (context-K K r)

sni-k-↑-e' : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) → SNi (K aₖ ↑ op V M) (suc n) → {L : Γ ⊢M[ ∅ ]⦂ Z} → K aₖ M ↝↝ L → SNi L n

sni-k-↑-e : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) → SNi (K aₖ ↑ op V M) n → SNi (K aₖ M) n

sni-k-↑-e' K (sn sM) r with aₖ→`aₖ K r
... | ↝id r = sni-k-↑-e id (sM (context-↑ r))
... | ↝∘l K r with sn sM ← sni-k-↑-e K (sM (context-K K (let-↑ _ _ _))) = sni-≤ (n≤1+n _) (sM (context-K K r))
... | ↝∘↓ K r with sn sM ← sni-k-↑-e K (sM (context-K K (↓-↑ _ _ _))) = sni-≤ (n≤1+n _) (sM (context-K K r))

sni-k-↑-e {n = suc n} K sM = sn (sni-k-↑-e' K sM)


-- AUXILIARY LEMMAS ON REDUCIBILITY OF CERTAIN EXTENSIONS OF CONTINUATIONS

kred-comm-let : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
                KRed (K ∘l L ∘l N) →
                ---------------------------------------------
                KRed (K ∘l (let= N `in M-rename (wk₂ wk₁) L))

kred-comm-let K rK rV =
  sn-let-return (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ let= _ `in z))
      eq (rK rV (context-K (K-rename _ K ∘l _) (let-return _ _))))
  where
  eq : M-rename (wk₂ r) L
       ≡
       M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (id-subst [ V ]s) ]m

  eq {r = r} {L = L} {V = V} =
    begin
      M-rename (wk₂ r) L
    ≡⟨ wk₂wk₁M[liftid-subst[W]] _ _ ⟩
      M-rename (wk₂ wk₁) (M-rename (wk₂ r) L) [ lift (id-subst [ V ]s) ]m
    ≡⟨ cong (_[ _ ]m) (trans ren-ren-l (sym ren-ren-l)) ⟩
      M-rename (wk₂ (wk₂ r)) (M-rename (wk₂ wk₁) L) [ lift (id-subst [ V ]s) ]m
    ∎

kred-comm-↓ : (K : Γ ⊢K⦂ Z ⊸ U [ n ]) →
              KRed (K ∘↓ op [ V ] ∘l N) →
              ----------------------
              KRed (K ∘l ↓ op (V-rename wk₁ V) N)

kred-comm-↓ K rK rV =
  sn-let-return (K-rename _ K)
    (subst (λ z → SN (K-rename _ K aₖ ↓ _ z _))
      eq (rK rV (context-K (K-rename _ K ∘↓ _ [ _ ]) (let-return _ _))))
  where
  eq : V-rename r W
       ≡
       V-rename (wk₂ r) (V-rename wk₁ W) [ id-subst [ V ]s ]v

  eq {r = r} {W = W} {V = V} =
    begin
      V-rename r W
    ≡⟨ wk₁V[id-subst[W]] _ _ ⟩
      V-rename wk₁ (V-rename r W) [ id-subst [ V ]s ]v
    ≡⟨ cong (_[ id-subst [ V ]s ]v) (trans (ren-ren-v {V = W}) (sym ren-ren-v)) ⟩
      V-rename (wk₂ r) (V-rename wk₁ W) [ id-subst [ V ]s ]v
    ∎

kred-↝ : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) →
         M ↝↝ N →
         KRed (K ∘l M) →
         --------------
         KRed (K ∘l N)

kred-↝ K r rK rV =
  sn-let-return (K-rename _ K)
    (sn→sn'
      (rK rV (context-K (K-rename _ K) (let-return _ _)))
      (context-K (K-rename _ K) (sub-↝↝ _ (ren-↝↝ _ r))))

kred-↑ : (K : Γ ⊢K⦂ Y ⊸ Z [ n ]) → KRed (K ∘l ↑ op V M) → KRed (K ∘l M)
kred-↑ K rK rV =
  sn-let-return (K-rename _ K)
    (sn'→sn (sn-k-↑-e (K-rename _ K) (rK rV (context-K (K-rename _ K) (let-return _ _)))))


-- CONTINUATIONS AND AWAITING CONTINUATIONS WHOSE BODY HAS BEEN SUBJECTED
-- TO A REINSTALL SUBSTITUTION ARE REDUCIBLE

kred-let-r : (K : Γ ⊢K⦂ ⟨ X ⟩ ⊸ Z [ n ]) →
             KRed K →
             CRedSubR' N →
             SN (K aₖ R) →
             ---------------------------------
             KRed (K ∘l N [ M-rename wk₁ R ]r)

kred-let-r {N = N} {R = R} K rK rN sR {r = r} {V = V} rV =
  sn-let-return (K-rename r K)
    (subst (λ z → SN (K-rename r K aₖ z)) (sym ([]r-wk-ren-sub r N R V))
      (sn'→sn (credr-kred (K-rename r K) (kred-r K rK) (rN rV) (sn-ren-aₖ K sR))))

ared-await-r : (K : Γ ⊢K⦂ ⟨ X ⟩ ⊸ Z [ n ]) →
               KRed K →
               CRedSubR' N →
               SN (K aₖ R) →
               ---------------------------------
               ARed K (N [ M-rename wk₁ R ]r)

ared-await-r {N = N} {R = R} K rK rN sR {r = r} {V = V} rV =
  sn-await (K-rename r K)
    (subst (λ z → SN (K-rename r K aₖ z)) (sym ([]r-wk-ren-sub r N R V))
      (sn'→sn (credr-kred (K-rename r K) (kred-r K rK) (rN rV) (sn-ren-aₖ K sR))))


-- INTERRUPT HANDLERS ARE REDUCIBLE

{- PROPOSITION 20 -}

sn-promise : (K : Γ ⊢K⦂ Y ⊸ Z [ k ]) →
             KRed (K ∘l N) →
             CRedSubR' M →
             SNi (K-rename wk₁ K aₖ N) n →
             -----------------------------------
             {L : Γ ⊢M[ ∅ ]⦂ Z} → K `aₖ promise op ↦ M `in N ↝↝ L → SN L

sn-promise K rK rM (sn h) (↝id (promise-↑ _ _ _)) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e id (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝id (context-promise r)) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))
sn-promise _ rK rM (sn h) (↝∘l K (let-promise _ _ _)) =
  sn'→sn (λ r → sn-promise K (kred-comm-let K rK) rM (sn h) (aₖ→`aₖ K r))
sn-promise K rK rM (sn h) (↝∘l K' (context-let (promise-↑ _ _ _))) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e (K-rename _ (K' ∘l _)) (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝∘l _ (context-let (context-promise r))) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))
sn-promise _ rK rM (sn h) (↝∘↓ K (↓-promise-op V M N)) =
  sn'→sn
    (subst (λ z → SN' (K aₖ let= z [ promise _ ↦ M `in return (` Hd) ]r `in ↓ _ (V-rename wk₁ V) N))
      (trans ren-id-m (cong (_[ id-subst [ V ]s ]m) ren-id-l))
      (rM {r = id-ren} tt {r = id-ren}
        (K ∘l ↓ _ (V-rename wk₁ V) N)
        (kred-comm-↓ K rK)
        (promise _ ↦ M `in return (` Hd))
        (sn'→sn (λ r →
          sn-promise
            (K ∘l ↓ _ (V-rename wk₁ V) N)
            (kred-let (K ∘l ↓ _ (V-rename wk₁ V) N) (kred-comm-↓ K rK) cred-return)
            rM
            (sn→sni (sn'→sn (sn-let-return (K-rename wk₁ K)
              (subst₂ (λ w u → SN (K-rename wk₁ K aₖ ↓ _ w u)) wk₂wk₁V[Hd] wk₂wk₁M[Hd] (sni→sn (sn h))))))
            (aₖ→`aₖ (K ∘l ↓ _ (V-rename wk₁ V) N) r)))))
sn-promise _ rK rM (sn h) (↝∘↓ K (↓-promise-op' _ _ _ _)) =
  sn'→sn (λ r → sn-promise K (kred-comm-↓ K rK) rM (sn h) (aₖ→`aₖ K r))
sn-promise K rK rM (sn h) (↝∘↓ K' (context-↓ (promise-↑ _ _ _))) =
  sn'→sn (sn-↑ K (sn'→sn (λ r → sn-promise K (kred-↑ K rK) rM (sni-k-↑-e (K-rename _ (K' ∘↓ _ [ _ ])) (sn h)) (aₖ→`aₖ K r))))
sn-promise K rK rM (sn h) (↝∘↓ _ (context-↓ (context-promise r))) =
  sn'→sn (λ r' → sn-promise K (kred-↝ K r rK) rM (h (context-K (K-rename wk₁ K) r)) (aₖ→`aₖ K r'))

cred-promise : CRedSubR' M → CRedSub' N → CRed (promise op ↦ M `in N)
cred-promise rM rN K rK r =
  sn-promise K (kred-let K rK (credsub'-r rN)) (credsubr'-r rM)
    (sn→sni (sn'→sn (cred-kred (K-rename _ K) (kred-r K rK) (credsub'→cred rN)))) (aₖ→`aₖ K r)


-- PROOFS OF THE REDUCIBILITY LEMMAS FOR HANDLER CODE (REINSTALL CONTEXT re X)

credr-return : {V : Γ ⊢V⦂ ⟨ X ⟩} → VRed V → CRedR (return V)
credr-return {V = V} rV K rK R sR = cred-return {V = V} rV K rK

credr-app : {V : Γ ⊢V⦂ Y ⇒ ⟨ X ⟩} {W : Γ ⊢V⦂ Y} → CRed (V · W) → CRedR (V · W)
credr-app rVW K rK R sR = rVW K rK

credr-reinstall : CRedR (reinstall {Γ = Γ} {X = X})
credr-reinstall K rK R sR = sn→sn' sR

credr-let : CRed M → CRedSubR' N → CRedR (let= M `in N)
credr-let rM rN K rK R sR = rM (K ∘l _) (kred-let-r K rK (credsubr'-r rN) sR)

credr-↑ : CRedR M → CRedR (↑ op V M)
credr-↑ rM K rK R sR = sn-↑ K (sn'→sn (rM K rK R sR))

credr-↓ : {M : Γ ⊢M[ ∅ ]⦂ ⟨ X ⟩} → CRed M → CRedR {X = X} (↓ op V M)
credr-↓ rM K rK R sR = cred-↓ rM K rK

credr-await : {V : Γ ⊢V⦂ ⟨ Y ⟩} {N : Γ ∷ Y ⊢M[ re X ]⦂ ⟨ X ⟩} → VRed V → CRedSubR' N → CRedR (await V until N)
credr-await rV rN K rK R sR = rV K _ (ared-await-r K rK (credsubr'-r rN) sR)

credr-promise : CRedSubR' M → CRedSubR' N → CRedR (promise op ↦ M `in N)
credr-promise rM rN K rK R sR r =
  sn-promise K (kred-let-r K rK (credsubr'-r rN) sR) (credsubr'-r rM)
    (sn→sni (sn'→sn (credr-kred (K-rename wk₁ K) (kred-r K rK) (credsubr'→credr rN) (sn-ren-aₖ K sR)))) (aₖ→`aₖ K r)


-- REDUCIBILITY IMPLIES STRONG NORMALISATION

cred→sn : CRed M → SN' M
cred→sn rM = subst SN' ren-id-m (rM id (λ _ ()))


-- REDUCIBLE SUBSTITUTIONS

SubRed : (s : Sub Γ Γ') → Set
SubRed {Γ} s = {X : Type} (x : X ∈ Γ) → VRed (s x)


-- PREDICATES EXPRESSING THAT ALL REDUCIBLE SUBSTITUTIONS OF A TERM ARE REDUCIBLE

VRedSub : Γ ⊢V⦂ X → Set
VRedSub {Γ} V = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → VRed (V [ s ]v)

CRedSub : Γ ⊢M[ ∅ ]⦂ X → Set
CRedSub {Γ} M = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → CRed (M [ s ]m)

CRedSubR : Γ ⊢M[ re X ]⦂ ⟨ X ⟩ → Set
CRedSubR {Γ} M = {Γ' : Ctx} {s : Sub Γ Γ'} → SubRed s → CRedR (M [ s ]m)


-- PROPERTIES OF THE ABOVE PREDICATES

subred-⨟ : SubRed s → SubRed (s ⨟ ren r)
subred-⨟ {r = r} rs x = subst VRed (sym ren-rename-v) (vred-r (rs x))

subred-[]s : SubRed s → VRed V → SubRed (s [ V ]s)
subred-[]s rs rV Hd = rV
subred-[]s rs rV (Tl x) = rs x

lift-⨟-eq : (M : Γ ∷ X ⊢M[ ρ ]⦂ Y) (s : Sub Γ Γ') (r : Ren Γ' Γ'') (V : Γ'' ⊢V⦂ X) →
            M [ (s ⨟ ren r) [ V ]s ]m
            ≡
            M-rename (wk₂ r) (M [ lift s ]m) [ id-subst [ V ]s ]m

lift-⨟-eq M s r V =
  begin
    M [ (s ⨟ ren r) [ V ]s ]m
  ≡⟨ M[lifts][id-subst[V]] _ _ ⟩
    M [ lift (s ⨟ ren r) ]m [ id-subst [ V ]s ]m
  ≡⟨ cong (_[ id-subst [ V ]s ]m) (cong-sub-m (λ x → trans (sym (lift-⨟ x)) (cong-sub-v {V = lift s x} (λ {Hd → refl; (Tl x) → refl})))) ⟩
    M [ lift s ⨟ ren (wk₂ r) ]m [ id-subst [ V ]s ]m
  ≡⟨ cong (_[ id-subst [ V ]s ]m) (sym sub-sub-m) ⟩
    M [ lift s ]m [ ren (wk₂ r) ]m [ id-subst [ V ]s ]m
  ≡⟨ cong (_[ id-subst [ V ]s ]m) ren-rename-m ⟩
    M-rename (wk₂ r) (M [ lift s ]m) [ id-subst [ V ]s ]m
  ∎

cred-⨟ : SubRed s → CRedSub M → CRedSub' (M [ lift s ]m)
cred-⨟ {s = s} {M = M} rs rM {r = r} {V = V} rV K rK =
  subst (λ z → SN' (K aₖ M-rename _ z)) (lift-⨟-eq M s r V) (rM (subred-[]s (subred-⨟ rs) rV) K rK)

credr-⨟ : SubRed s → CRedSubR M → CRedSubR' (M [ lift s ]m)
credr-⨟ {s = s} {M = M} rs rM {r = r} {V = V} rV K rK R sR =
  subst (λ z → SN' (K aₖ M-rename _ z [ R ]r)) (lift-⨟-eq M s r V) (rM (subred-[]s (subred-⨟ rs) rV) K rK R sR)


-- THE FUNDAMENTAL THEOREM OF LOGICAL RELATIONS

fund-v : (V : Γ ⊢V⦂ X) → VRedSub V

fund-m : (M : Γ ⊢M[ ∅ ]⦂ X) → CRedSub M

fund-mr : (M : Γ ⊢M[ re X ]⦂ ⟨ X ⟩) → CRedSubR M

fund-v (` x) rs = rs x
fund-v (`` c) rs = tt
fund-v (ƛ M) rs = vred-ƛ (cred-⨟ rs (fund-m M))
fund-v ⟨ V ⟩ rs = vred-⟨⟩ (fund-v V rs)

fund-m (return V) rs = cred-return (fund-v V rs)
fund-m (V · W) rs = subst (λ z → CRed (z · _)) ren-id-v (fund-v V rs (fund-v W rs))
fund-m (↑ op V M) rs = cred-↑ (fund-m M rs)
fund-m (promise op ↦ M `in N) rs = cred-promise (credr-⨟ rs (fund-mr M)) (cred-⨟ rs (fund-m N))
fund-m (await V until M) rs = cred-await (fund-v V rs) (cred-⨟ rs (fund-m M))
fund-m (let= M `in N) rs = cred-let (fund-m M rs) (cred-⨟ rs (fund-m N))
fund-m (↓ op V M) rs = cred-↓ (fund-m M rs)

fund-mr (return V) rs = credr-return (fund-v V rs)
fund-mr (V · W) rs = credr-app (subst (λ z → CRed (z · _)) ren-id-v (fund-v V rs (fund-v W rs)))
fund-mr reinstall rs {r = r} = credr-reinstall {r = r}
fund-mr (↑ op V M) rs = credr-↑ (fund-mr M rs)
fund-mr (promise op ↦ M `in N) rs = credr-promise (credr-⨟ rs (fund-mr M)) (credr-⨟ rs (fund-mr N))
fund-mr (await V until M) rs = credr-await (fund-v V rs) (credr-⨟ rs (fund-mr M))
fund-mr (let= M `in N) rs = credr-let (fund-m M rs) (credr-⨟ rs (fund-mr N))
fund-mr (↓ op V M) rs = credr-↓ (fund-m M rs)


-- ALL TERMS ARE REDUCIBLE AND STRONGLY NORMALISING

all-terms-red : (M : Γ ⊢M[ ∅ ]⦂ X) → CRed M
all-terms-red M rewrite sym (sub-id-m {M = M}) = fund-m M vred-var

strong-norm : (M : Γ ⊢M[ ∅ ]⦂ X) → SN M
strong-norm M = sn'→sn (cred→sn (all-terms-red M))

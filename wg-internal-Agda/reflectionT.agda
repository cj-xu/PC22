{-# OPTIONS --rewriting #-}

{--------------------
Can we use Agda's reflection mechanism to cheaply write terms in
internal languages in Agda?

Work in progress.
--------------------}

open import Data.List as List
open import Data.Unit
open import Reflection hiding (_>>=_)
open import Reflection.AST.Show
open import Reflection.AST.Argument.Information

open import Data.Product
open import Data.Nat
open import Data.Maybe hiding (_>>=_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function

-- Types of System T
data typ : Set where
  ι : typ
  _⇒_ : typ -> typ -> typ

-- Domain and codomain extractions for cong purposes
domain : typ → typ
domain ι = ι
domain (t ⇒ _) = t

codomain : typ → typ
codomain ι = ι
codomain (_ ⇒ t) = t

-- Decidable equality for types
decEqTyp : (t t' : typ) → Dec (t ≡ t')
decEqTyp ι ι = yes refl
decEqTyp ι (t ⇒ t') = no λ ()
decEqTyp (t ⇒ t') ι = no (λ ())
decEqTyp (t ⇒ t') (s ⇒ s') with decEqTyp t s | decEqTyp t' s'
... | yes p | yes q = yes (cong₂ _⇒_ p q)
... | no p | _ = no λ r → p (cong domain r)
... | _ | no p = no λ r → p (cong codomain r)

-- A lemma to rewrite with, so we don't get stuck on neutral `t`
decEqTyp-refl : (t : typ) → decEqTyp t t ≡ yes refl
decEqTyp-refl ι = refl
decEqTyp-refl (t ⇒ t') rewrite decEqTyp-refl t | decEqTyp-refl t' = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE decEqTyp-refl #-}

-- Typing contexts
data Ctxt : Set where
  · : Ctxt
  _,_ : Ctxt -> typ -> Ctxt

infixl 4 _,_
infix 3 _∈_

-- Evidence of membership
data _∈_ : typ → Ctxt -> Set where
  here : ∀ {t Γ} → t ∈ Γ , t
  there : ∀ {t t' Γ} → t ∈ Γ → t ∈ Γ , t'

-- Convert numeric position to evidence of membership, or fail
fromIndex : ℕ → (Γ : Ctxt)(t : typ) → TC (t ∈ Γ)
fromIndex n · t = typeError (strErr "empty context" ∷ [])
fromIndex zero (Γ , t') t with decEqTyp t t'
... | yes refl = return here
... | no p = typeError (strErr "types" ∷ termErr (quoteTerm t) ∷ strErr "and " ∷ termErr (quoteTerm t') ∷ strErr "not equal" ∷ [])
fromIndex (suc n) (Γ , t') t = do
  p <- fromIndex n Γ t
  return (there p)
  where _>>=_ = Reflection._>>=_

-- Convert numeric position to evidence of membership, down-to-earth Maybe version
fromIndex' : ℕ → (Γ : Ctxt)(t : typ) → Maybe (t ∈ Γ)
fromIndex' n · t = nothing
fromIndex' zero (Γ , t') t with decEqTyp t t'
... | yes refl = just here
... | no p = nothing
fromIndex' (suc n) (Γ , t') t = do
  p <- fromIndex' n Γ t
  just (there p)
  where _>>=_ = Data.Maybe._>>=_

-- System T terms, well-typed by construction
data T : Ctxt -> typ -> Set where
  var : ∀ {Γ t} → t ∈ Γ → T Γ t
  _·_ : ∀ {Γ t t'} → T Γ (t ⇒ t') → T Γ t → T Γ t'
  ƛ : ∀ {Γ t t'} → T (Γ , t) t' → T Γ (t ⇒ t')
  zer : ∀ {Γ} → T Γ ι
  succ : ∀ {Γ} → T Γ (ι ⇒ ι)
  -- recursor

-- Package up term as standard argument
mkArg : Term → Arg Term
mkArg t = arg ainfo t where
  ainfo : ArgInfo
  ainfo = arg-info visible (Reflection.modality relevant quantity-ω)

-- Translation from Agda terms to T Γ t datatype
translate : (Γ : Ctxt) → (t : typ) → Term → TC Term
translate Γ ty (var x []) = do -- TODO: non-empty args
    p <- fromIndex x Γ ty
    p' <- quoteTC p
    return (con (quote T.var) (mkArg p' ∷ []))
    where _>>=_ = Reflection._>>=_
translate Γ (ty ⇒ ty') (lam v (abs x t)) = do
  t' <- translate (Γ , ty) ty' t
  return (con (quote ƛ) (mkArg t' ∷ []))
  where _>>=_ = Reflection._>>=_
translate Γ ty t = return t

-- Same translation from Agda terms to T Γ t datatype, using Maybe instead of TC
translate' : (Γ : Ctxt) → (t : typ) → Term → Maybe (T Γ t)
translate' Γ ty (var x []) = do -- TODO: non-empty args
    p <- fromIndex' x Γ ty
    just (T.var p)
    where _>>=_ = Data.Maybe._>>=_
translate' Γ (ty ⇒ ty') (lam v (abs x t)) = do
  t' <- translate' (Γ , ty) ty' t
  just (ƛ t')
  where _>>=_ = Data.Maybe._>>=_
translate' Γ ty t = nothing


-- Magic to make TC work
macro
  extract : Ctxt -> typ -> Term -> Term -> TC ⊤
  extract Γ ty t hole = do
    t' <- translate Γ ty t
    unify hole t'
    where _>>=_ = Reflection._>>=_


test : ∀ {Γ t} → T Γ (t ⇒ t)
test {Γ} {t} = extract Γ (t ⇒ t) (λ (x : Set) → x)
-- C-C C-n test: λ {Γ} {t} → ƛ (var here)


-- Alternatively:
test' : ∀ {Γ t} → Maybe (T Γ (t ⇒ t))
test' {Γ} {t} = translate' Γ (t ⇒ t) (quoteTerm (λ (x : Set) → x))
-- C-C C-n test': λ {Γ} {t} → just (ƛ (var here))

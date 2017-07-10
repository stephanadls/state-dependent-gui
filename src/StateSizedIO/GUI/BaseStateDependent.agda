{-# OPTIONS --allow-unsolved-metas #-}

module StateSizedIO.GUI.BaseStateDependent where

open import Size renaming (Size to AgdaSize)
open import NativeIO
open import Function
open import Agda.Primitive
open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Product
open import Relation.Binary.PropositionalEquality

record IOInterfaceˢ {γ ρ μ} : Set (lsuc (γ ⊔ ρ ⊔ μ )) where
  field
    Stateˢ    : Set γ
    Commandˢ  : Stateˢ → Set ρ
    Responseˢ : (s : Stateˢ) → Commandˢ s → Set μ
    nextˢ     : (s : Stateˢ) → (c : Commandˢ s) → Responseˢ s c → Stateˢ
open IOInterfaceˢ public

module _  {γ ρ μ}(i   : IOInterfaceˢ {γ} {ρ} {μ} )
                                (let S = Stateˢ i)     (let C  = Commandˢ i)
                                (let  R  = Responseˢ i) (let next = nextˢ i)


  where
    mutual
      record IOˢ {α} (i : AgdaSize)  (A : S → Set α) (s : S) : Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
        coinductive
        constructor delay
        field
          forceˢ : {j : Size< i} → IOˢ' j A s

      data IOˢ' {α} (i : AgdaSize)  (A : S → Set α) : S → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
        doˢ'     : {s : S} → (c : C s) → (f : (r : R s c) → IOˢ i A (next s c r) )
                   → IOˢ' i A s
        returnˢ' : {s : S} → (a : A s) → IOˢ' i A s

    data IOˢ+ {α} (i : AgdaSize)  (A : S → Set α ) : S → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ )) where
      doˢ' : {s : S} → (c : C s) (f : (r : R s c) → IOˢ i A  (next s c r))
            → IOˢ+ i A s

    IOₚˢ : ∀{α}(i : AgdaSize)(A : Set α)(t t' : S) → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ ))
    IOₚˢ i A t t' = IOˢ i (λ s → s ≡ t' × A) t

    IOₚˢ' : ∀{α}(i : AgdaSize)(A : Set α)(t t' : S) → Set (lsuc (α ⊔ γ ⊔ ρ ⊔ μ ))
    IOₚˢ' i A t t' = IOˢ' i (λ s → s ≡ t' × A) t

    IOₚsemiˢ : ∀{i}{α}{β}{A : Set α }{B : S → Set β}{t : S}
               (t' : A → S) → Set (lsuc α ⊔ (lsuc μ ⊔ (lsuc ρ ⊔ lsuc γ)))
    IOₚsemiˢ{i}{α}{β}{A}{B}{t} t' = IOˢ i (λ s → Σ[ a ∈ A ] (s ≡ t' a)) t

{-
Add also this later:
IO A t t'     where t' : A -> S
Programs which start in t end with an a : A and a state t' a
IO A t t' = IO   (lambda s.Sigma a : A. s = t' a) t
>==   : (p : IO A t t') (f : (a : A) ->  IO  B (t' a) ) ->   IO B a
-}

open IOˢ public


module _  {α γ ρ μ}{I   : IOInterfaceˢ {γ} {ρ} {μ}}
                   (let S = Stateˢ I)     (let C  = Commandˢ I)
                   (let  R  = Responseˢ I) (let next = nextˢ I) where
  returnˢ : ∀{i}{A : S → Set α} {s : S} (a : A s) → IOˢ  I i A s
  forceˢ (returnˢ a) = returnˢ' a

  doˢ  : ∀{i}{A : S → Set α}{s : S}
         (c : C s)
         (f : (r : R s c) → IOˢ I i A (next s c r))
         → IOˢ I i A s
  forceˢ (doˢ c f) = doˢ' c f


module _  {α β γ ρ μ}{I   : IOInterfaceˢ {γ} {ρ} {μ}}
                   (let S = Stateˢ I)     (let C  = Commandˢ I)
                   (let  R  = Responseˢ I) (let next = nextˢ I) where

  mutual  -- TODO: check that next state is honored
    fmapˢ : ∀ {i} → {A : S → Set α}{B : S → Set β}
                      (f : (s : S)(a : A s) → B s)
                      {s : S}
                      (p : (IOˢ I i A s))
                      → IOˢ I i B s
    fmapˢ f {s} p .forceˢ = fmapˢ' f {s} (p .forceˢ)


    fmapˢ' : ∀ {i} → {A : S → Set α}{B : S → Set β}
                      (f : (s : S)(a : A s) → B s)
                      {s : S}
                      (p : (IOˢ' I i A s))
                      → IOˢ' I i B s
    fmapˢ' f {s} (doˢ' c g) = doˢ' c  (λ r → fmapˢ f (g r))
    fmapˢ' f {s} (returnˢ' a) = returnˢ' (f s a)



module _  {α γ ρ μ}{I   : IOInterfaceˢ {γ} {ρ} {μ}}
                   (let S = Stateˢ I)     (let C  = Commandˢ I)
                   (let  R  = Responseˢ I) (let next = nextˢ I) where

  delayˢ : ∀ {i}{A : S → Set α}{s : S} → IOˢ' I i A s → IOˢ I (↑ i) A s
  delayˢ p .forceˢ = p


module _  {γ ρ μ}{I   : IOInterfaceˢ {γ} {ρ} {μ}}
                   (let S = Stateˢ I)     (let C  = Commandˢ I)
                   (let  R  = Responseˢ I) (let next = nextˢ I) where

  mutual

    _>>=ˢ'_ : ∀{i α β}{A : S → Set α}{B : S → Set β}{t : S}
               (m : IOˢ' I i A t)
               (f : (s : S)(a : A s) → IOˢ I (↑ i) B s)
               → IOˢ' I i B t
    doˢ' c f >>=ˢ' k = doˢ' c λ x → f x >>=ˢ k
    _>>=ˢ'_ {_} {_} {_} {_} {_} {t} (returnˢ' a) f =  f t a .forceˢ

    _>>=ˢ_ : ∀{i α β}{A : S → Set α}{B : S → Set β}{t : S}
             (m : IOˢ I i A t)
             (k : (s : S)(a : A s) → IOˢ I i B s)
             → IOˢ I i B t
    forceˢ (m >>=ˢ k) = (forceˢ m) >>=ˢ' k


    _>>=ₚˢ'_ : ∀{i}{α}{β}{A : Set α }{B : S → Set β}{t t' : S}
               (p : IOˢ' I i (λ s → s ≡ t' × A) t)
               (f : (a : A) → IOˢ I (↑ i) B t')
               → IOˢ' {γ} {ρ} {μ}  I i B t
    _>>=ₚˢ'_ {i} {α} {β} p  f =  p >>=ˢ' (λ s → λ {(refl , a) → f a})



    _>>=ₚˢ_ : ∀{i}{α}{β}{A : Set α }{B : S → Set β}{t t' : S}
               (p : IOˢ I i (λ s → s ≡ t' × A) t)
               (f : (a : A) → IOˢ I (↑ i) B t')
               → IOˢ I i B t
    _>>=ₚˢ_ {i} {α} {β} p  f = p >>=ˢ (λ s → λ {(refl , a) → f a})




    _>>=ₚsemiˢ_ : ∀{i}{α}{β}{A : Set α }{B : S → Set β}{t : S}
               {t' : A → S}
               -- IOs starts in t, returns a, and ends in a state t' a:
               (p : IOˢ I i (λ s → Σ[ a ∈ A ] (s ≡ t' a)) t)
               (f : (a : A) → IOˢ I (↑ i) B (t' a))
               → IOˢ I i B t
    _>>=ₚsemiˢ_ {i} {α} {β}{A}{B}{t}{t'} p f = p >>=ˢ f'
      module aux where
      f' : (s : Stateˢ I) → Σ[ a ∈ A ] (s ≡ t' a) → IOˢ I i B s
      f' .(t' a) (a , refl) = f a





module _  {γ ρ}{I   : IOInterfaceˢ {γ} {ρ} {lzero}}
                (let S = Stateˢ I)     (let C  = Commandˢ I)
                (let  R  = Responseˢ I) (let next = nextˢ I) where
  {-# NON_TERMINATING #-}

  translateIOˢ : ∀{A : Set }{s : S}
    →  (translateLocal : (s : S) → (c : C s) → NativeIO (R s c))
    →  IOˢ I ∞ (λ s → A) s
    →  NativeIO A
  translateIOˢ {A} {s} translateLocal p = case (forceˢ p {_}) of
    λ{ (doˢ' {.s} c f)    → (translateLocal s c)     native>>= λ r →
                             translateIOˢ translateLocal (f r)
     ; (returnˢ' a) → nativeReturn a
     }

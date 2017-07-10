module GUIgeneric.GUIFeaturesPart3 where

open import GUIgeneric.Prelude renaming (addButton to addButton')

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.GUI.WxGraphicsLibLevel3 renaming (addButton to addButton')
open import GUIgeneric.GUIFeatures
open import GUIgeneric.GUIFeaturesPart2 hiding ( main )
open import GUIgeneric.GUIExample hiding (main )


open import Data.Product
open import Data.Fin


liftResultˢ : (S S' : Set) (s2GUI : (s : S') → Frame)
             (ss' : S → S')
             (s : S)
             (m : methodsG (s2GUI (ss' s)))
             (r : Resultˢ (handlerGUIInterfₛ S (s2GUI ∘ ss')) s m)
            → Resultˢ (handlerGUIInterfₛ S' s2GUI) (ss' s) m
liftResultˢ S S' s2GUI ss' s m noChange = noChange
liftResultˢ S S' s2GUI ss' s m (changedState snew) = changedState (ss' snew)


extendHandlerGuiInterfₛ :  (i : Size)
                           (S S' : Set) (s2GUI : (s : S') → Frame)
                           (ss' : S → S')
                           (s : S)
                           (obj : handlerGUIObjectₛ i S (s2GUI ∘ ss') s)
                           → handlerGUIObjectₛ i S' s2GUI (ss' s)
method (extendHandlerGuiInterfₛ i S S' s2GUI ss' s obj) m =
                    x >>= (λ r → return (liftResultˢ S S' s2GUI ss' s m r))
              where
                      x : IO GuiLev1Interface ∞  (Resultˢ (handlerGUIInterfₛ S (s2GUI ∘ ss')) s m)
                      x = method obj m

lift⊎3  : {A B C : Set} → A ⊎ B → A ⊎ B ⊎ C
lift⊎3 (inj₁ x) = inj₁ x
lift⊎3 (inj₂ y) = inj₂ (inj₁ y)


mapReturnTypeₛ : {A B : Set}(f : A → B) (a : ReturnTypeₛ A) → ReturnTypeₛ  B
mapReturnTypeₛ f noChange = noChange
mapReturnTypeₛ f (changedState snew) = changedState (f snew)

mapStateMachineHandl : {S S' : Set}(f : S → S')
                       (p : IO GuiLev1Interface ∞ (ReturnTypeₛ S))
                       → IO GuiLev1Interface ∞ (ReturnTypeₛ S')
mapStateMachineHandl f p = mapIO (mapReturnTypeₛ f) p

mapSMachineState : {S S' : Set}(f : S → S')(s : S)(sm : SMachineState S s)
                    → SMachineState S' (f s)
mapSMachineState f s sm .fSM = sm .fSM
mapSMachineState f s sm .propSM = sm .propSM
mapSMachineState f s sm .handlSM m = mapStateMachineHandl f (sm .handlSM m)

mapFMachineHandle : {A B C : Set}
                          (a : A ⊎ B)(sm : SMachineState (A ⊎ B) a)
                          → SMachineState (A ⊎ B ⊎ C) (lift⊎3 a)
mapFMachineHandle a sm = mapSMachineState lift⊎3 a sm

mapIOFeatureM : {A B C : Set}
            → IO GuiLev1Interface ∞ (ReturnTypeₛ (A ⊎ B))
            → IO GuiLev1Interface ∞ (ReturnTypeₛ (A ⊎ B ⊎ C))
mapIOFeatureM p = mapIO (mapReturnTypeₛ lift⊎3) p


Cancel : FMachine StateV → FMachine StateV
Cancel vm .Features = vm .Features × FeatureCancel
Cancel vm .AddStateF  = vm .AddStateF ⊎ ⊤
Cancel vm .GUIF (f , yesCancel) (inj₁ s1) =
      addBtn2StateMachine (mapFMachineHandle (inj₁ s1) (vm .GUIF f (inj₁ s1)))
                          "Cancel" ((inj₂ (inj₂ _)))
Cancel vm .GUIF (f , _) (inj₁ s) = mapFMachineHandle (inj₁ s) (vm .GUIF f (inj₁ s))
Cancel vm .GUIF (f , _) (inj₂ (inj₁ x)) = mapFMachineHandle (inj₂ x) (vm .GUIF f (inj₂ x))
Cancel vm .GUIF (f , _) (inj₂ (inj₂ _)) = simpleSMState "Intermediate" (inj₁ s0)

Tea : FMachine StateV → FMachine StateV
Tea vm .Features = vm .Features × FeatureTea
Tea vm .AddStateF  = vm .AddStateF ⊎ ⊤
Tea vm .GUIF (f , yeTea) (inj₁ s2) =
      addBtn2StateMachine (mapFMachineHandle (inj₁ s2) (vm .GUIF f (inj₁ s2)))
                          "Tea" ((inj₂ (inj₂ _)))
Tea vm .GUIF (f , _) (inj₁ s) = mapFMachineHandle (inj₁ s) (vm .GUIF f (inj₁ s))
Tea vm .GUIF (f , _) (inj₂ (inj₁ x)) = mapFMachineHandle (inj₂ x) (vm .GUIF f (inj₂ x))
Tea vm .GUIF (f , _) (inj₂ (inj₂ _)) = simpleSMState "Get Your Tea" (inj₁ s0)


cancelBase : FMachine StateV
cancelBase = Cancel baseF

teaCancelBase : FMachine StateV
teaCancelBase = Tea cancelBase

main : NativeIO Unit
main = compileFeatureVM teaCancelBase ((_ , yesCancel) , yesTea) (inj₁ s0) --

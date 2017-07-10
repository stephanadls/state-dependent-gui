module GUIgeneric.GUIFeaturesPart4 where

open import GUIgeneric.Prelude renaming (addButton to addButton')

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.GUI.WxGraphicsLibLevel3 renaming (addButton to addButton')
open import GUIgeneric.GUIFeatures
open import GUIgeneric.GUIFeaturesPart2 hiding ( main )
open import GUIgeneric.GUIFeaturesPart3 hiding ( main )
open import GUIgeneric.GUIExample hiding (main )


open import Data.Product
open import Data.Fin

addStateFMachine  : {BaseState : Set}
                          (vm : FMachine BaseState)
                          (Snew : Set)
                          (newSM : (s : Snew) →
                            SMachineState (BaseState ⊎ vm .AddStateF ⊎ Snew) (inj₂ (inj₂ s)))
                         → FMachine BaseState
addStateFMachine {BaseState} vm Snew newSM .Features = vm .Features
addStateFMachine {BaseState} vm Snew newSM .AddStateF = vm .AddStateF ⊎ Snew
addStateFMachine {BaseState} vm Snew newSM .GUIF f (inj₁ s) =
                mapFMachineHandle (inj₁ s) (vm .GUIF f (inj₁ s))
addStateFMachine {BaseState} vm Snew newSM .GUIF f (inj₂ (inj₁ s)) =
                mapFMachineHandle (inj₂ s) (vm .GUIF f (inj₂ s))
addStateFMachine {BaseState} vm Snew newSM .GUIF f (inj₂ (inj₂ s)) .fSM = newSM s .fSM
addStateFMachine {BaseState} vm Snew newSM .GUIF f (inj₂ (inj₂ s)) .propSM = newSM s .propSM
addStateFMachine {BaseState} vm Snew newSM .GUIF f (inj₂ (inj₂ s)) .handlSM = newSM s .handlSM

addOneStateFMachine  : {BaseState : Set}
                          (vm : FMachine BaseState)
                          (newSM : SMachineState (BaseState ⊎ vm .AddStateF ⊎ ⊤) (inj₂ (inj₂ _)))
                         → FMachine BaseState
addOneStateFMachine vm newSM = addStateFMachine vm ⊤ λ _ → newSM


addDummyFeatures  : {BaseState : Set}
                                  (vm : FMachine BaseState)
                                  (FeatureNew : Set)
                                   → FMachine BaseState
addDummyFeatures vm FeatureNew .Features = vm .Features × FeatureNew
addDummyFeatures vm FeatureNew .AddStateF = vm .AddStateF
addDummyFeatures vm FeatureNew .GUIF (f , _) s = vm .GUIF f s





{- handler for the new state to be added to the cancel machine -}
cancelNewStateSM : (vm : FMachine StateV) →
                    SMachineState (StateV ⊎ vm .AddStateF ⊎ ⊤) (inj₂ (inj₂ tt))
cancelNewStateSM vm = simpleSMState "Intermediate" (inj₁ s0)

{- add the state to the old feature machine -}
cancelStateAdded : FMachine StateV → FMachine StateV
cancelStateAdded vm = addOneStateFMachine vm (cancelNewStateSM vm)

{- add a dummy feature "FeatureCancel" to the feature machine -}
cancelFeatureAdded : FMachine StateV → FMachine StateV
cancelFeatureAdded vm = addDummyFeatures
                         (cancelStateAdded vm)
                         FeatureCancel

{- redefine in the feature machine one button -}
Cancel' : FMachine StateV → FMachine StateV
Cancel' vm .Features = cancelFeatureAdded vm .Features
Cancel' vm .AddStateF  = cancelFeatureAdded vm .AddStateF
Cancel' vm .GUIF (f , yesCancel) (inj₁ s1) =
      addBtn2StateMachine (cancelFeatureAdded vm .GUIF (f , yesCancel) (inj₁ s1))
                          "Cancel" (inj₂ (inj₂ _))
Cancel' vm .GUIF f  s = cancelFeatureAdded vm .GUIF f s


main : NativeIO Unit
main = compileFeatureVM (Cancel' baseF) (_ , yesCancel) (inj₁ s0) --

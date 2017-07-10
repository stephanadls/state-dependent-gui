-- {-# OPTIONS --allow-unsolved-metas #-}
module GUIgeneric.GUIFeaturesPart5 where

open import GUIgeneric.Prelude renaming (addButton to addButton')

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.GUI.WxGraphicsLibLevel3 renaming (addButton to addButton')
open import GUIgeneric.GUIFeatures
open import GUIgeneric.GUIFeaturesPart2 hiding ( main ; main1 )
open import GUIgeneric.GUIFeaturesPart3 hiding ( main ; Tea ; Cancel)
open import GUIgeneric.GUIFeaturesPart4 hiding ( main ; cancelNewStateSM ; cancelStateAdded ; cancelFeatureAdded  )
open import GUIgeneric.GUIExample hiding (main )



data StatesBasicVM : Set where
  pay change soda serveSoda  open' close : StatesBasicVM

basicVM : FMachine StatesBasicVM
basicVM  .Features = ⊤
basicVM  .AddStateF = ⊥
basicVM  .GUIF f (inj₁ pay)        =
         simpleSMState "Pay" (inj₁ change)
basicVM  .GUIF f (inj₁ change)     =
         simpleSMState "Get Change" (inj₁ soda)
basicVM  .GUIF f (inj₁ soda)       =
         simpleSMState "Soda" (inj₁ serveSoda)
basicVM  .GUIF f (inj₁ serveSoda)  =
         simpleSMState "Serve Soda" (inj₁ open')
basicVM  .GUIF f (inj₁ open')      =
         simpleSMState "Open" (inj₁ close)
basicVM  .GUIF f (inj₁ close)      =
         simpleSMState "Close" (inj₁ pay) 
basicVM  .GUIF f (inj₂ ())

newState : {A B : Set} → A ⊎ B ⊎ ⊤
newState = (inj₂ (inj₂ tt))

{- handler for the new state to be added to the tea machine -}
teaNewStateSM :  (fm : FMachine StatesBasicVM)
                 →    SMachineState
                      (StatesBasicVM ⊎ fm .AddStateF ⊎ ⊤)
                      newState
teaNewStateSM fm = simpleSMState "Serve Tea" (inj₁ open')

{- add the new state to the feature machine -}
TeaMAddNewState :  FMachine StatesBasicVM
                   → FMachine StatesBasicVM
TeaMAddNewState fm =
  addOneStateFMachine fm (teaNewStateSM fm)

{- add a dummy feature "FeatureTea" to the feature machine -}
TeaMAddFeature :  FMachine StatesBasicVM
                  → FMachine StatesBasicVM
TeaMAddFeature fm = addDummyFeatures
                         (TeaMAddNewState fm)
                         FeatureTea

{- redefine in the feature machine one button -}
Tea :  FMachine StatesBasicVM
       → FMachine StatesBasicVM
Tea fm .Features   = TeaMAddFeature fm .Features
Tea fm .AddStateF  = TeaMAddFeature fm .AddStateF
Tea fm .GUIF (f , yesTea) (inj₁ soda) =
      addBtn2StateMachine
      (  TeaMAddFeature fm .GUIF
         (f , yesTea) (inj₁ soda))
         "Tea" newState
Tea fm .GUIF f  s = TeaMAddFeature fm .GUIF f s

{- handler for the new state to be added to the cancel machine -}
cancelNewStateSM : (fm : FMachine StatesBasicVM) →
                    SMachineState (StatesBasicVM ⊎ fm .AddStateF ⊎ ⊤) newState
cancelNewStateSM fm = simpleSMState "Cancelling" (inj₁ pay)

{- add the state to the old feature machine -}
cancelStateAdded : FMachine StatesBasicVM → FMachine StatesBasicVM
cancelStateAdded fm = addOneStateFMachine fm (cancelNewStateSM fm)

{- add a dummy feature "FeatureCancel" to the feature machine -}
cancelFeatureAdded : FMachine StatesBasicVM → FMachine StatesBasicVM
cancelFeatureAdded fm = addDummyFeatures
                         (cancelStateAdded fm)
                         FeatureCancel

{- redefine in the feature machine one button -}
Cancel :  FMachine StatesBasicVM
          → FMachine StatesBasicVM
Cancel fm .Features = cancelFeatureAdded fm .Features
Cancel fm .AddStateF  = cancelFeatureAdded fm .AddStateF
Cancel fm .GUIF (f , yesCancel) (inj₁ soda) =
      addBtn2StateMachine (cancelFeatureAdded fm .GUIF (f , yesCancel) (inj₁ soda))
                          "Cancel" newState
Cancel fm .GUIF f  s = cancelFeatureAdded fm .GUIF f s

{- add the Dummy free feature -}
FreeMAddFeature : FMachine StatesBasicVM
                  → FMachine StatesBasicVM
FreeMAddFeature fm = addDummyFeatures fm FeatureFree

{- redefine the pay button to free in case feature free is yesFree -}
Free :  FMachine StatesBasicVM
        → FMachine StatesBasicVM
Free fm .Features   = FreeMAddFeature fm .Features
Free fm .AddStateF  = FreeMAddFeature fm .AddStateF
Free fm .GUIF (f , yesFree) (inj₁ pay) =
      simpleSMState "Free" (inj₁ soda)
Free fm .GUIF (f , yesFree) (inj₁ open') =
      simpleSMState "Skip" (inj₁ pay)
Free fm .GUIF f  s  = FreeMAddFeature fm .GUIF f s

main1 : NativeIO Unit
main1 = compileFeatureVM (Tea (Cancel basicVM)) ((_ , yesCancel) , yesTea) (inj₁ pay)

main2 : NativeIO Unit
main2 = compileFeatureVM (Free basicVM) (_ , yesFree) (inj₁ pay) --

multiFeatureMachine : FMachine StatesBasicVM
multiFeatureMachine = Free (Cancel (Tea basicVM))

main : NativeIO Unit
main = compileFeatureVM
       multiFeatureMachine
       (((_ , yesTea) , yesCancel) , noFree) (inj₁ pay)

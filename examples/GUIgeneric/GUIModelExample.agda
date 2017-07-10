open import Data.Bool
module GUIgeneric.GUIModelExample  where

open import GUIgeneric.Prelude renaming (inj₁ to secondButton; inj₂ to firstButton; WxColor to Color) hiding (IOInterfaceˢ)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add; ComponentEls to Frame)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods
open import StateSizedIO.Base
open import GUIgeneric.GUIExample using (oneBtnGUI ; propOneBtn ; obj1Btn; twoBtnGUI ; propTwoBtn ; obj2Btn )
open import GUIgeneric.GUIModel
open import Data.Sum

open IOInterfaceˢ public


private postulate btn  :  FFIButton
private postulate fr   :  FFIFrame

state1Btn : ModelGuiState
state1Btn = state  oneBtnGUI propOneBtn
                   (obj1Btn {∞}) notStarted

state2Btn : ModelGuiState
state2Btn = state  twoBtnGUI propTwoBtn
                   (obj2Btn {∞}) notStarted


corstate1BtnNext1∀  : (m : ModelGuiState)
                      → (state1Btn -gui->¹ m)
                      →  m ≡ state2Btn
corstate1BtnNext1∀ m (step _) = refl

corstate1BtnNext∃   : state1Btn -gui->¹ state2Btn
corstate1BtnNext∃ =  step (btn , fr)


corstate1BtnNext∀  : (m : ModelGuiState)
                     → (state2Btn -gui->¹ m)
                     →  (m ≡ state2Btn ⊎ m ≡ state1Btn )
corstate1BtnNext∀ m  (step (inj₁ _)) = inj₁ refl
corstate1BtnNext∀ m  (step (inj₂ _)) = inj₂ refl

corstate2BtnNext∃1   : state2Btn -gui->¹ state2Btn
corstate2BtnNext∃1 =  step (inj₁ (btn , (btn , fr)) )

corstate2BtnNext∃2   : state2Btn -gui->¹ state1Btn
corstate2BtnNext∃2 =  step (inj₂ (btn , (btn , fr)) )

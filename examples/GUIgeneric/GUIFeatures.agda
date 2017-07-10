module GUIgeneric.GUIFeatures where

open import GUIgeneric.Prelude

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.GUI.WxGraphicsLibLevel3


open Interfaceˢ public



-- Components
--
frameAndOKButton : ComponentEls _
frameAndOKButton = add (create-button "OK button") create-frame notOptimzed

exampleOneButton : Frame
exampleOneButton = frameAndOKButton

exampleTwoButtons : Frame
exampleTwoButtons = add (create-button "Cancel button") frameAndOKButton notOptimzed

exampleThreeButtons : Frame
exampleThreeButtons = add (create-button "Cancel button") (frameAndOKButton) notOptimzed

getFrame : Frame → ComponentEls frame
getFrame (createC tt) = create-frame
getFrame (add' buttonFrame f f₁ _) = f₁



data StateV : Set where
      s0 s1 s2 : StateV

data StateTea : Set where
      s0 s1 s2 s3 : StateTea

data FeatureTea : Set where
  yesTea noTea : FeatureTea

data FeatureFree : Set where
  yesFree noFree : FeatureFree

data FeatureCancel : Set where
  yesCancel noCancel : FeatureCancel


record FeatureVendingMachine (BaseState : Set) : Set₁ where
  field  Features : Set
         AddState : Set
         guiVendingMachine : (f : Features) → BaseState ⊎ AddState → Frame
  NewState : Set
  NewState =  BaseState ⊎ AddState


open FeatureVendingMachine public


base : FeatureVendingMachine StateV
base .Features = ⊤
base .AddState = ⊥
base .guiVendingMachine f (inj₁ s0) = exampleOneButton
base .guiVendingMachine f (inj₁ s1) = exampleOneButton
base .guiVendingMachine f (inj₁ s2) = exampleTwoButtons
base .guiVendingMachine f (inj₂ ())


upgradeFeatureVM : (baseState : Set)(vm : FeatureVendingMachine baseState)
                   → FeatureVendingMachine (baseState ⊎ vm .AddState)
upgradeFeatureVM baseState vm .Features = vm .Features
upgradeFeatureVM baseState vm .AddState = ⊥
upgradeFeatureVM baseState vm .guiVendingMachine f (inj₁ (inj₁ s)) = vm .guiVendingMachine f (inj₁ s)
upgradeFeatureVM baseState vm .guiVendingMachine f (inj₁ (inj₂ s)) = vm .guiVendingMachine f (inj₂ s)
upgradeFeatureVM baseState vm .guiVendingMachine f (inj₂ ())



changeBaseState : (baseState : Set)(vm : FeatureVendingMachine baseState)
                  (newState : Set)
                  (new2base : newState → baseState)
                  → FeatureVendingMachine newState
changeBaseState baseState vm newState new2base  .Features = vm .Features
changeBaseState baseState vm newState new2base .AddState  = vm .AddState
changeBaseState baseState vm newState new2base .guiVendingMachine f (inj₁ x) = vm .guiVendingMachine f (inj₁ (new2base x))
changeBaseState baseState vm newState new2base .guiVendingMachine f (inj₂ y) = vm .guiVendingMachine f (inj₂ y)





upgradeFeatureVM+ : (baseState : Set)(vm : FeatureVendingMachine baseState)
                    (newBaseState : Set)
                    (newAddState : Set)
                    (new2base : newBaseState ⊎ newAddState → baseState ⊎ vm .AddState)
                     → FeatureVendingMachine newBaseState
Features (upgradeFeatureVM+ baseState vm newBaseState newAddState new2Base) = vm .Features
AddState (upgradeFeatureVM+ baseState vm newBaseState newAddState new2Base) = newAddState
guiVendingMachine (upgradeFeatureVM+ baseState vm newBaseState newAddState new2Base)  f s = vm .guiVendingMachine f (new2Base s)




tea : FeatureVendingMachine StateV → FeatureVendingMachine StateV
tea otherVM .Features = otherVM .Features × FeatureTea
tea otherVM .AddState = otherVM .AddState ⊎ ⊤
tea otherVM .guiVendingMachine (f , yesTea) (inj₁ s1) = exampleThreeButtons
tea otherVM .guiVendingMachine (f , _) (inj₁ s) = otherVM .guiVendingMachine f (inj₁ s)
tea otherVM .guiVendingMachine (f , _) (inj₂ (inj₁ s)) = otherVM .guiVendingMachine f (inj₂ s)
tea otherVM .guiVendingMachine (f , _) (inj₂ (inj₂ _)) = exampleOneButton -- new state


cancel : FeatureVendingMachine StateV → FeatureVendingMachine StateV
cancel otherVM .Features = otherVM .Features × FeatureCancel
cancel otherVM .AddState = otherVM .AddState ⊎ ⊤
cancel otherVM .guiVendingMachine (f , yesCancel) (inj₁ s1) = exampleThreeButtons
cancel otherVM .guiVendingMachine (f , _) (inj₁ s) = otherVM .guiVendingMachine f (inj₁ s)
cancel otherVM .guiVendingMachine (f , _) (inj₂ (inj₁ s)) = otherVM .guiVendingMachine f (inj₂ s)
cancel otherVM .guiVendingMachine (f , _) (inj₂ (inj₂ _)) = exampleOneButton -- new state



teaBase : FeatureVendingMachine StateV
teaBase = tea base

StateTeaAux  : Set
StateTeaAux = StateV ⊎ (⊥ ⊎ ⊤)

teaBaseUnified : FeatureVendingMachine StateTeaAux
teaBaseUnified = upgradeFeatureVM StateV teaBase

stateTeaToPrevState : StateTea → StateTeaAux
stateTeaToPrevState s0 = inj₁ s0
stateTeaToPrevState s1 = inj₁ s1
stateTeaToPrevState s2 = inj₁ s2
stateTeaToPrevState s3 = inj₂ (inj₂ _)

teaBaseImproved : FeatureVendingMachine StateTea
teaBaseImproved = changeBaseState
                       StateTeaAux
                       teaBaseUnified StateTea stateTeaToPrevState

teaBaseNewToOld : StateTea ⊎ ⊥ → StateV ⊎ teaBase .AddState
teaBaseNewToOld (inj₁ s0) = inj₁ s0
teaBaseNewToOld (inj₁ s1) = inj₁ s1
teaBaseNewToOld (inj₁ s2) = inj₁ s2
teaBaseNewToOld (inj₁ s3) = inj₂ (inj₂ _)
teaBaseNewToOld (inj₂ ())

teaBaseImproved+ : FeatureVendingMachine StateTea
teaBaseImproved+  = upgradeFeatureVM+ StateV teaBase StateTea ⊥ teaBaseNewToOld

cancelTeaBase = cancel (tea base)





module base' where
  NewFeatures' : Set
  NewFeatures' = ⊤

  guiVendingMachine' : (f : NewFeatures') → StateV → Frame
  guiVendingMachine' f s0 = exampleOneButton
  guiVendingMachine' f s1 = exampleOneButton
  guiVendingMachine' f s2 = exampleTwoButtons


module tea' (OtherFeatures : Set)
           (oldV : OtherFeatures  → StateV → Frame) where
  NewFeatures' : Set
  NewFeatures' = OtherFeatures × FeatureTea

  guiVendingMachine' : (f : NewFeatures')(s : StateV) → Frame
  guiVendingMachine' (f , yesTea) s1 = exampleThreeButtons
  guiVendingMachine' (f , _) s = oldV f s


module cancel' (OtherFeatures : Set)
              (oldV : OtherFeatures → StateV → Frame) where
  NewFeatures' : Set
  NewFeatures' = OtherFeatures × FeatureCancel


  guiVendingMachine' : (f : NewFeatures')(s : StateV) → Frame
  guiVendingMachine' (f , yesCancel) s1 = exampleThreeButtons
  guiVendingMachine' (f , _) s = oldV f s


module teaBase' (OtherFeatures : Set) where
  open base' renaming (guiVendingMachine' to baseGUIVendingMachine; NewFeatures' to BaseFeatures)
  open tea' BaseFeatures baseGUIVendingMachine public



module cancelTeaBase' (OtherFeatures : Set) where
  open teaBase' OtherFeatures renaming (guiVendingMachine' to teaBaseGUIVendingMachine; NewFeatures' to TeaBaseFeatures)
  open cancel' TeaBaseFeatures teaBaseGUIVendingMachine

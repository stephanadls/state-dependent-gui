open import Data.Bool

module GUIgeneric.GUIExample   where

open import GUIgeneric.Prelude renaming (inj₁ to secondBtn; inj₂ to firstBtn; WxColor to Color) hiding (addButton; _>>_)


open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib renaming (addButton to addButton')

open import Data.Product

addButton : String → Frame → Frame
addButton str fr = addButton' str fr optimized

addTxtBox : String → Frame → Frame
addTxtBox str fr = addTxtBox' str fr optimized



oneBtnGUI : Frame
oneBtnGUI = addButton "OK" create-frame

twoBtnGUI : Frame
twoBtnGUI = addButton "Cancel" oneBtnGUI



-- Attributes
--
Cols = ℕ
Margin  = ℕ
HSpace  = ℕ
VSpace  = ℕ

oneColumnLayout : Cols × Margin × HSpace × VSpace
oneColumnLayout = (1 , 10 , 2 , 2)



black : Color
black = rgb 0 0 0

propOneBtn : properties oneBtnGUI
propOneBtn = black , oneColumnLayout

propTwoBtn : properties twoBtnGUI
propTwoBtn = black , black , oneColumnLayout



putStr' : {A : Set} → String → (f : IO GuiLev1Interface ∞ A) →
           IO GuiLev1Interface ∞ A
putStr' s f = do (putStrLn s) (λ _ → f)

syntax putStr' s f = putStrLn s >> f


keepGUI : {j : Size} → HandlerObject j twoBtnGUI →
            IO GuiLev1Interface ∞
      (Σ-syntax (returnType twoBtnGUI)
       (λ r →
          IOObjectˢ GuiLev1Interface handlerInterface j
          (nextStateFrame twoBtnGUI r)))
keepGUI = λ obj → return (noChange , obj)


changeGUI : ∀ {j} (g : CompEls frame) {g'} (prop : properties g) obj →
              IO GuiLev1Interface ∞ (Σ (returnType g') (\r -> IOObjectˢ GuiLev1Interface handlerInterface j (nextStateFrame g' r)))
changeGUI = λ g prop obj →  return (changedGUI g prop , obj)



mutual
 objTwoBtnGUI' : ∀ i → HandlerObject i twoBtnGUI
 objTwoBtnGUI' i .method {j} (secondBtn bt) =
   putStrLn "Cancel Fired! NO GUI Change." >>
   keepGUI (objTwoBtnGUI' j)

 objTwoBtnGUI' i .method {j} (firstBtn bt) =
   putStrLn "OK Fired! Redefining GUI." >>
   changeGUI oneBtnGUI propOneBtn (objOneBtnGUI' j)

 objOneBtnGUI' : ∀ i → HandlerObject i oneBtnGUI
 objOneBtnGUI' i .method {j} bt =
    putStrLn "OK Fired! Redefining GUI." >>
    changeGUI twoBtnGUI propTwoBtn (objTwoBtnGUI' j)


 obj2Btn : ∀ {i} → HandlerObject i twoBtnGUI
 obj2Btn .method (firstBtn bt) =
   putStrLn "OK fired! Redefining GUI." >>
   changeGUI oneBtnGUI propOneBtn obj1Btn
 obj2Btn .method (secondBtn bt) =
   putStrLn "Cancel fired! No GUI change." >>
   keepGUI obj2Btn

 obj1Btn : ∀ {i} → HandlerObject i oneBtnGUI
 obj1Btn .method bt =
    putStrLn "OK fired! Redefining GUI." >>
    changeGUI twoBtnGUI propTwoBtn obj2Btn


main : NativeIO Unit
main = compileProgram  twoBtnGUI propTwoBtn
                       (obj2Btn {∞})

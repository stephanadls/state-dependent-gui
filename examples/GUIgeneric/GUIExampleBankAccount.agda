module GUIgeneric.GUIExampleBankAccount   where

open import GUIgeneric.Prelude renaming (inj₁ to firstBtn; inj₂ to secondBtn; WxColor to Color;_∸_ to _-_) hiding (addButton; _>>_ ; show)


open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib renaming (addButton to addButton')
open import GUIgeneric.GUIExample  hiding (main; changeGUI)

open import Data.Nat.Show
open import heap.libraryNat renaming (_≧ℕb_ to _≧_)





guifullToReturnType : ∀ {i} {g} → GUI {i} → returnType g
guifullToReturnType f = changedGUI (f .defFrame) (f .property)

guifullToReturnType' : ∀ {i} {g} → GUI {i} →
                       Σ[ r ∈ returnType g ]
                       (IOObjectˢ GuiLev1Interface handlerInterface i
                           (nextStateFrame g r))
guifullToReturnType' {i} {g} f = guifullToReturnType f , f .obj

changeGUI : ∀ {i} {g} → GUI {i} →
                       IO GuiLev1Interface ∞ (Σ[ r ∈ returnType g ]
                       (IOObjectˢ GuiLev1Interface handlerInterface i
                           (nextStateFrame g r)))
changeGUI  f = return (guifullToReturnType' f)

threeBtnFrame : (s s' s'' : String) → Frame
threeBtnFrame s s'  s'' = addButton s  (addButton s'
                             (addButton s'' create-frame))



propThreeBtn : ∀{s s' s''} → properties (threeBtnFrame s s' s'')
propThreeBtn = black , black , black , oneColumnLayout



mutual
 atm :  ∀{i} → ℕ → GUI {i}
 atm n   .defFrame  =
      addButton  "Withdraw 10"
     (addButton  "Withdraw 1"
     (addTxtBox  (show n) create-frame))
 atm n   .property =
   black , black , black , oneColumnLayout
 atm n   .obj .method (firstBtn x) =
    if n ≧ 10  then  changeGUI  (atm (n - 10))
               else  changeGUI  (invalid n)

 atm n  .obj .method (secondBtn b) =
     if n ≧ 1  then  changeGUI  (atm (n - 1))
               else  changeGUI  (invalid n)



 invalid : ∀{i} → ℕ → GUI {i}
 invalid n .defFrame =
     addButton "Not enough money" create-frame
 invalid n .property       =  black , oneColumnLayout
 invalid n .obj .method m  =  changeGUI (atm n)




main : NativeIO Unit
main = compileGUI (atm 55)

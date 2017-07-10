

module GUIgeneric.GUIExampleLib where

open import GUIgeneric.Prelude  hiding (addButton)

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI



executeChangeGui : ∀{i} → (fr : FFIFrame)(mvar : MVar StateAndGuiObj)
                          (mvarFFI : MVar StateAndFFIComp)
                          (let state = addVar mvar (SingleMVar mvarFFI))
      → StateAndGuiObj × StateAndFFIComp →
      IOˢ GuiLev2Interface i (λ _ → prod state) state

executeChangeGui fr varO varFFI ((gNew , (prop , obj)) , (gOld , ffi)) =

  deleteComp gOld ffi >>=ₚˢ λ _ →
  reCreateFrame gNew fr >>=ₚˢ λ ffiNew →
  setHandlerG gNew ffiNew varO (SingleMVar varFFI)  >>=ₚˢ λ _ →

  (translateLev1toLev2 (setAttributes ∞ gNew prop ffiNew)) >>=ˢ λ _ _ →
  returnˢ ((gNew , (prop , obj)) , (gNew , ffiNew ))




setRightClick₃ : ∀{i} →
                      (g : Frame)
                      (ffiComp : FFIcomponents g)
                      (mvar : MVar StateAndGuiObj)
                      (mvarFFI : MVar StateAndFFIComp)
                      (getFr : FFIcomponents g → FFIFrame)
                      (let state = addVar mvar (SingleMVar mvarFFI))
                      → IOˢ GuiLev3Interface i (λ s → s ≡ state × Unit) state

setRightClick₃ g ffi mvar mvarFFI getFr =
  doˢ (setRightClick (getFr ffi)
                     (executeChangeGui (getFr ffi) mvar mvarFFI ∷ [])) λ r →
  returnˢ (refl , _)

setCustomEvent₃ : ∀{i} →
                      (g : Frame)
                      (ffiComp : FFIcomponents g)
                      (mvar : MVar StateAndGuiObj)
                      (mvarFFI : MVar StateAndFFIComp)
                      (getFr : FFIcomponents g → FFIFrame)
                      (let state = addVar mvar (SingleMVar mvarFFI))
                      → IOˢ GuiLev3Interface i (λ s → s ≡ state × Unit) state

setCustomEvent₃ g ffi mvar mvarFFI getFr =
  doˢ (setCustomEvent (getFr ffi)
                     (executeChangeGui (getFr ffi) mvar mvarFFI ∷ [])) λ r →
  returnˢ (refl , _)


mainGeneric : (g : Frame)(a : properties g)(o : HandlerObject ∞ g)(getFr : FFIcomponents g → FFIFrame)
           → IOˢ GuiLev3Interface ∞ (λ _ → Unit) []

mainGeneric g propDef objDef getFr =
 let _>>=_ = _>>=ₚˢ_
     createGUIElements = λ g → cmd3 (createFrame g)
     setAttributes = λ g prop ffi → cmd3 (translateLev1toLev2ₚ (setAttributes ∞ g prop ffi))

 in
 createGUIElements g         >>=  λ ffi →
 setAttributes g propDef ffi >>=  λ _ →

 cmd3 (initFFIMVar g ffi)                             >>=ₚsemiˢ λ mvaffi →

 cmd3 (initHandlerMVar (SingleMVar mvaffi) g propDef objDef)  >>=ₚsemiˢ λ mvar →
 cmd3 (setHandlerG g ffi mvar (SingleMVar mvaffi))    >>=ₚˢ λ _ →
 setCustomEvent₃ g ffi mvar mvaffi getFr              >>=ˢ λ _ _ →

  returnˢ _
    where
      cmd3 = translateLev2toLev3



compileProgram : (g : Frame)(a : properties g) (h : HandlerObject ∞ g)
                  → NativeIO Unit
compileProgram g a h  = start (translateLev3 (mainGeneric g a h (getFrameGen g)))

generateProgram = compileProgram

addButton : String → CompEls frame → (isOpt : IsOptimized) → CompEls frame
addButton str fr isOpt = add' buttonFrame (create-button str) fr isOpt

addTxtBox' : String → CompEls frame → (isOpt : IsOptimized) → CompEls frame
addTxtBox' str fr isOpt = add' buttonFrame (create-txtbox str) fr isOpt



record GUI {i : Size} : Set₁ where 
   field   
      defFrame  : Frame
      property  : properties defFrame
      obj       : HandlerObject i defFrame
open GUI public

guiFull2IOˢprog : GUI → IOˢ GuiLev3Interface ∞ (λ _ → Unit) []
guiFull2IOˢprog g = mainGeneric (g .defFrame) (g .property) (g .obj) (getFrameGen (g .defFrame))

compileGUI : GUI → NativeIO Unit
compileGUI g = start (translateLev3 (guiFull2IOˢprog g))

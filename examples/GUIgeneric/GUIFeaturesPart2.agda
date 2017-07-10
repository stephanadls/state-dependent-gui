module GUIgeneric.GUIFeaturesPart2 where

open import GUIgeneric.Prelude renaming (addButton to addButton')

open import GUIgeneric.GUIDefinitions renaming (add to add'; add' to add)
open import GUIgeneric.GUI
open import GUIgeneric.GUIExampleLib
open import StateSizedIO.GUI.WxGraphicsLibLevel3 renaming (addButton to addButton')
open import GUIgeneric.GUIFeatures
open import GUIgeneric.GUIExample using (propOneBtn; propTwoBtn ; black ; oneColumnLayout)

open import Data.Product
open import Data.Fin

data ReturnTypeₛ  (S : Set) : Set where
    noChange      : ReturnTypeₛ S
    changedState  : (snew : S) →  ReturnTypeₛ S


-- handler GUI interface with separte state (i.e. state is a separte set instead of GUI)
-- We might later separte State into a gui state and property state i.e. have
--  GuiState : Set
--  AttrState : GuiState → Set
--  s2GUI : GuiState → GUI
--  s2prop : (g : GuiState)(prop : AttrState g) → properties (s2GUI g)

handlerGUIInterfₛ  : (S : Set) (s2GUI : (s : S) → Frame)
                     → Interfaceˢ
handlerGUIInterfₛ S s2GUI .Stateˢ                        = S
handlerGUIInterfₛ S s2GUI .Methodˢ  s                    = methodsG (s2GUI s)
handlerGUIInterfₛ S s2GUI .Resultˢ  s m                  = ReturnTypeₛ S
handlerGUIInterfₛ S s2GUI .nextˢ s m noChange            = s
handlerGUIInterfₛ S s2GUI .nextˢ s m (changedState snew) = snew

handlerGUIObjectₛ : (i : Size)(S : Set) (s2GUI : (s : S) → Frame)(s : S) → Set
handlerGUIObjectₛ i S s2GUI s = IOObjectˢ- GuiLev1Interface (handlerGUIInterfₛ S s2GUI) i s

mutual
  hGuiObjₛ2ord : (i : Size)(S : Set)
                 (s2GUI : (s : S) → Frame)
                 (s2prop : (s : S) → properties (s2GUI s))
                 (obj :  (s : S) → handlerGUIObjectₛ i S s2GUI s)
                 (s : S)
                 → HandlerObject i (s2GUI s)
  method (hGuiObjₛ2ord i S s2GUI s2prop obj s) {j} m =
        hGuiObjₛ2ordaux ∞  j  S s2GUI s s2prop obj m (method (obj s) m )

  hGuiObjₛ2ordaux' : (j : Size)(j' : Size)(S : Set)
                  (s2GUI : (s : S) → Frame)(s : S)
                  (s2prop : (s : S) → properties (s2GUI s))
                  (obj :  (s : S) → handlerGUIObjectₛ j' S s2GUI s)
                  (m   : methodsG (s2GUI s))
                  (prog : IO' GuiLev1Interface j
                            (ReturnTypeₛ S))
                  → IO' GuiLev1Interface j
                         ( Σ[ r ∈ returnType (s2GUI s) ]
                            (IOObjectˢ GuiLev1Interface handlerInterface j'
                             (nextˢ handlerInterface (s2GUI s) m r)))
  hGuiObjₛ2ordaux' j j' S s2GUI s s2prop obj m (do' c f) = do' c (λ r → hGuiObjₛ2ordaux j j' S s2GUI s s2prop obj m  (f r) )
  hGuiObjₛ2ordaux' j j' S s2GUI s s2prop obj m (return' noChange ) = return' (noChange , hGuiObjₛ2ord j' S s2GUI s2prop obj s {-obj'-})
  hGuiObjₛ2ordaux' j j' S s2GUI s s2prop obj m (return' (changedState snew)) = return' (changedGUI (s2GUI snew) (s2prop snew) , hGuiObjₛ2ord j' S s2GUI s2prop obj snew {- obj'-})


  hGuiObjₛ2ordaux : (j : Size)(j' : Size)(S : Set)
                  (s2GUI : (s : S) → Frame)(s : S)
                  (s2prop : (s : S) → properties (s2GUI s))
                  (obj :  (s : S) → handlerGUIObjectₛ j' S s2GUI s)
                  (m   : methodsG (s2GUI s))
                  (prog : IO GuiLev1Interface j
                            (ReturnTypeₛ S))
                  → IO GuiLev1Interface j
                         ( Σ[ r ∈  returnType (s2GUI s) ]
                            (IOObjectˢ GuiLev1Interface handlerInterface j'
                             (nextˢ handlerInterface (s2GUI s) m r)))
  force (hGuiObjₛ2ordaux j j' S s2GUI s s2prop obj m pr) {j''} = hGuiObjₛ2ordaux' j'' j' S s2GUI s s2prop obj m (force pr)




{-   *** STATE MACHINES  **** -}


sMachineHdl : (S : Set)(s : S) (f  : Frame) → Set
sMachineHdl S s f =  (m : methodsG f)
              → IO GuiLev1Interface ∞ (ReturnTypeₛ S)

record SMachineState (S : Set)(s : S) : Set where 
  field
    fSM     : Frame
    propSM  : properties fSM
    handlSM : sMachineHdl S s fSM

SMachine : Set → Set
SMachine S = (s : S) → SMachineState S s

open SMachineState public


SMachine2HandlerGuiObjectₛ : (S : Set)
                             (sm : SMachine S)
                             (s : S)
                             → handlerGUIObjectₛ ∞ S (λ s → sm s .fSM) s
method (SMachine2HandlerGuiObjectₛ S sm s) = sm s .handlSM







stateMachine2Obj : (S : Set)
                   (sm : SMachine S)
                   (s : S)
                   → HandlerObject ∞ (sm s .fSM)
stateMachine2Obj S sm = hGuiObjₛ2ord ∞ S
                        (λ s → sm s .fSM)
                        (λ s → sm s .propSM)
                        (λ s → SMachine2HandlerGuiObjectₛ S sm s)

stateMachine2GUI : (S : Set) (sm : SMachine S) (s : S) → GUI
stateMachine2GUI S sm s .defFrame = sm s .fSM
stateMachine2GUI S sm s .property = sm s .propSM
stateMachine2GUI S sm s .obj = stateMachine2Obj S sm s

compileSMachine :  {S : Set} (sm : SMachine S) (s : S)
                   → NativeIO Unit
compileSMachine {S} sm s =
         compileGUI (stateMachine2GUI S sm s)


{-  **************** FEATURE MACHINE **** -}

-- an example of a feature machine wihout additional states:

record FeatureVMVers1 : Set₁ where 
  field
    Features  : Set
    State     : Set
    GUIF      : (f : Features) → SMachine State


record FMachine (BaseSt : Set) : Set₁ where 
  field  
     Features : Set
     AddStateF : Set
     GUIF      : (f : Features) → SMachine (BaseSt ⊎ AddStateF) 
  State : Set
  State =  BaseSt ⊎ AddStateF 

open FMachine public

featureVMFull2GUI : (BaseSt : Set)
                        (vm : FMachine BaseSt)
                        (f : vm .Features)
                        (s : State vm)
                        → GUI
featureVMFull2GUI BaseSt vm f s =
         stateMachine2GUI
              (BaseSt ⊎ vm .AddStateF)
              (vm .GUIF f)  s

featureVMFull2IOˢprog : {BaseSt : Set}
                        (vm : FMachine BaseSt)
                        (f : vm .Features)
                        (s : State vm) → IOˢ GuiLev3Interface ∞ (λ _ → Unit) []
featureVMFull2IOˢprog {BaseSt} vm f s = guiFull2IOˢprog (featureVMFull2GUI BaseSt vm f s)

compileFeatureVM : {BaseSt : Set}
                   (vm : FMachine BaseSt)
                   (f : vm .Features)
                   (s : State vm)
                    → NativeIO Unit
compileFeatureVM {BaseSt} vm f s = compileGUI (featureVMFull2GUI BaseSt vm f s)


{- methodsREduce creates from a method for the frame (addButon s g)
    a method for g -}

mutual
  methodsReduce : (g : Frame)(str : String)(m : MethodsStruct)
                  (u : methodsStruct2Method (addButton str g notOptimzed) m)
                  → methodsStruct2Method g m
  methodsReduce g str (fficom) (ffibtn , gcomp) = gcomp
  methodsReduce g str (⊥^) ()
  methodsReduce g str (m ⊎^unoptimized m₁) (inj₁ x) = inj₁ (methodsReduce g str m x)
  methodsReduce g str (m ⊎^unoptimized m₁) (inj₂ y) = inj₂ (methodsReduce g str m₁ y)
  methodsReduce g str (m ⊎^ m₁) x = methodsReduceaux g str m m₁
                                      (methodsUnivIsEmpty m)
                                      (methodsUnivIsEmpty m₁) x


  methodsReduceaux : (g : Frame)(str : String)(m : MethodsStruct)
                     (m₁ : MethodsStruct)
                     (s  : SemiDec (λ g' → methodsStruct2Method g'  m))
                     (s₁  : SemiDec (λ g' → methodsStruct2Method g' m₁))
                     (u : methodsStruct2Methodaux
                          (addButton str g notOptimzed) m m₁ s s₁)
                     → methodsStruct2Methodaux g  m m₁ s s₁
  methodsReduceaux g str m m₁ s (isEmpty s₁) u = methodsReduce g str m u
  methodsReduceaux g str m m₁ (isEmpty x) posNonEmpty u = methodsReduce g str m₁ u
  methodsReduceaux g str m m₁ posNonEmpty posNonEmpty (inj₁ x) = inj₁ (methodsReduce g str m x)
  methodsReduceaux g str m m₁ posNonEmpty posNonEmpty (inj₂ y) = inj₂ (methodsReduce g str m₁ y)







subMethodToFullMethod : (btnStr : String)
                        (fr     : Frame)
                        (m      : methodsStruct2Method (addButton btnStr fr notOptimzed)
                                   (methodStruct fr ))
                        → methodsG fr
subMethodToFullMethod btnStr fr m = methodsReduce fr btnStr (methodStruct fr ) m


simpleAttr1Btn : (btnStr : String) → properties (addButton btnStr create-frame notOptimzed)
simpleAttr1Btn btnStr = black , oneColumnLayout

simpleSMState : {S : Set}
                (btnStr : String)
                {start : S}
                (end : S)
                → SMachineState S start
simpleSMState btnStr end .fSM = addButton btnStr create-frame notOptimzed
simpleSMState btnStr end .propSM = simpleAttr1Btn btnStr
simpleSMState btnStr end .handlSM m .force  = return' (changedState end)

baseF : FMachine StateV
baseF .Features = ⊤
baseF .AddStateF = ⊥
baseF .GUIF f (inj₁ s0) = simpleSMState "1Euro" (inj₁ s1)
baseF .GUIF f (inj₁ s1) = simpleSMState "Get Change" (inj₁ s2)
baseF .GUIF f (inj₁ s2) = simpleSMState "Soda" (inj₁ s0)
baseF .GUIF f (inj₂ ())


addBtn2StateMachine : {S : Set}{s : S}(sm : SMachineState S s)
                      (btnStr : String)(end : S)
                      → SMachineState S s
addBtn2StateMachine sm btnStr end .fSM = addButton btnStr (sm .fSM) notOptimzed
addBtn2StateMachine sm btnStr end .propSM = black , sm .propSM
addBtn2StateMachine sm btnStr end .handlSM (inj₁ x) .force = return' (changedState end)
addBtn2StateMachine sm btnStr end .handlSM (inj₂ m) =
      sm .handlSM (subMethodToFullMethod btnStr (sm .fSM) m)

simpleCancel : FMachine StateV → FMachine StateV
simpleCancel vm .Features = vm .Features × FeatureCancel
simpleCancel vm .AddStateF  = vm .AddStateF
simpleCancel vm .GUIF (f , yesCancel) (inj₁ s1) =
          addBtn2StateMachine  (vm .GUIF f (inj₁ s1)) "Cancel"  (inj₁ s0)

simpleCancel vm .GUIF (f , _) s = vm .GUIF f s



simpleCancelBase : FMachine StateV
simpleCancelBase = simpleCancel baseF

main1 : NativeIO Unit
main1 = compileFeatureVM baseF _ (inj₁ s0) --


main : NativeIO Unit
main = compileFeatureVM simpleCancelBase (_ , yesCancel) (inj₁ s0) --

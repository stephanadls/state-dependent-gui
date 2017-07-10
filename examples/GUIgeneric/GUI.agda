

module GUIgeneric.GUI  where

open import GUIgeneric.Prelude
open import GUIgeneric.GUIDefinitions



Frame : Set
Frame  = ComponentEls frame

logOn : Bool
logOn = true

log : {A : Set} → String → (f : Unit → IO GuiLev1Interface ∞ A) →
         IO GuiLev1Interface ∞ A
log s f = if logOn then (do (putStrLn s) λ x → f x) else f unit

module _ where
  FFIcomponents : {c : Component}(e :  ComponentEls c) → Set
  FFIcomponents {c} (add i e e' _) = FFIcomponents e × FFIcomponents e'
  FFIcomponents {frame} (createC tt) = FFIFrame
  FFIcomponents {atomicComp} (createC (button x)) = FFIButton
  FFIcomponents {atomicComp} (createC (txtbox y)) = FFITextCtrl


  ffiComponentsToFrame : (e : ComponentEls frame)(ffi : FFIcomponents e) → FFIFrame
  ffiComponentsToFrame (createC x) ffi = ffi
  ffiComponentsToFrame (add c'c e e₁ _) (ffie , ffie₁) = ffiComponentsToFrame e₁ ffie₁


  FFIcomponentsReduce : {c c' : Component}(e : ComponentEls c)(e' : ComponentEls c')
                      (ee' : e <c e')
                      (ff1 : FFIcomponents e')
                       → FFIcomponents e
  FFIcomponentsReduce e (add i .e e'' _) (addsub i' .e .e'' _) ffi1 = proj₁ ffi1
  FFIcomponentsReduce e (add i e' .e _) (addlift i' .e' .e _) ffi1 = proj₂ ffi1


  FFIcomponentsReduce+ : {c c' : Component}(e : ComponentEls c)(e' : ComponentEls c')
                      (ee' : e <=c+ e')
                      (ffi : FFIcomponents e')
                       → FFIcomponents e
  FFIcomponentsReduce+ e .e (in0= .e) ffi1 = ffi1
  FFIcomponentsReduce+ e e' (in2= .e e'₁ .e' x ee') ffi1 =
    FFIcomponentsReduce e e'₁ x (FFIcomponentsReduce+ e'₁ e' ee' ffi1)




  data SemiDec (A : Frame → Set) : Set where
    isEmpty     : ((f : Frame) → A f → ⊥) → SemiDec A
    posNonEmpty : SemiDec A

  data MethodsStruct : Set where
      fficom : MethodsStruct
      ⊥^     : MethodsStruct
      _⊎^_   : (m m' : MethodsStruct) → MethodsStruct
      _⊎^unoptimized_   : (m m' : MethodsStruct) → MethodsStruct

  mutual

    methodsStruct2Method : (g : Frame)(m : MethodsStruct)  → Set
    methodsStruct2Method g fficom = FFIcomponents g
    methodsStruct2Method g ⊥^ = ⊥
    methodsStruct2Method g (m ⊎^ m₁) = methodsStruct2Methodaux g m m₁
                                        (methodsUnivIsEmpty  m)
                                        (methodsUnivIsEmpty  m₁)
    methodsStruct2Method g (m ⊎^unoptimized m₁) = methodsStruct2Method g m ⊎ methodsStruct2Method g m₁



    methodsStruct2Methodaux :  (g : Frame) (m m' : MethodsStruct)
                           (s  : SemiDec (λ g → methodsStruct2Method g m))
                           (s' : SemiDec (λ g → methodsStruct2Method g m'))
                           → Set
    methodsStruct2Methodaux g m m' s (isEmpty s') = methodsStruct2Method g m
    methodsStruct2Methodaux g m m' (isEmpty x) posNonEmpty = methodsStruct2Method g m'
    methodsStruct2Methodaux g m m' posNonEmpty posNonEmpty = methodsStruct2Method g m ⊎ methodsStruct2Method g m'

    methodsUnivIsEmpty : (m : MethodsStruct) → SemiDec (λ g → methodsStruct2Method g m)
    methodsUnivIsEmpty  fficom = posNonEmpty
    methodsUnivIsEmpty  ⊥^ = isEmpty (λ g → λ ())
    methodsUnivIsEmpty  (m ⊎^ m₁) =
                methodsUnivIsEmptyaux  m m₁
                  (methodsUnivIsEmpty   m)
                  (methodsUnivIsEmpty  m₁)
    methodsUnivIsEmpty  (m ⊎^unoptimized m₁) = posNonEmpty




    methodsUnivIsEmptyaux :  (m m' : MethodsStruct)
                           (s  : SemiDec (λ g → methodsStruct2Method g m ))
                           (s' : SemiDec (λ g → methodsStruct2Method g m' ))
                           → SemiDec (λ g → methodsStruct2Methodaux g m m' s s')
    methodsUnivIsEmptyaux  m m' s (isEmpty s') = s
    methodsUnivIsEmptyaux  m m' (isEmpty x) posNonEmpty = posNonEmpty
    methodsUnivIsEmptyaux  m m' posNonEmpty posNonEmpty = posNonEmpty

  inj₁MUaux : (g : Frame) (m m' : MethodsStruct)
                   (s  : SemiDec (λ g → methodsStruct2Method g m ))
                   (s'  : SemiDec (λ g → methodsStruct2Method g m' ))
                   (u : methodsStruct2Method g m)
                   → methodsStruct2Methodaux g m m' s s'
  inj₁MUaux g m m' s (isEmpty x) u = u
  inj₁MUaux g m m' (isEmpty x) posNonEmpty u = ⊥-elim (x g u)
  inj₁MUaux g m m' posNonEmpty posNonEmpty u = inj₁ u

  inj₁MUoptimized : (g : Frame) (m m' : MethodsStruct)(u : methodsStruct2Method g m )-- (isOpt : Bool)
                   → methodsStruct2Method g (m ⊎^ m') --isOpt
  inj₁MUoptimized g m m' u = inj₁MUaux g m m'
                         (methodsUnivIsEmpty  m)
                         (methodsUnivIsEmpty  m') u

  inj₁MUUnoptimized : (g : Frame) (m m' : MethodsStruct)(u : methodsStruct2Method g m )-- (isOpt : Bool)
                   → methodsStruct2Method g (m ⊎^unoptimized m') --isOpt
  inj₁MUUnoptimized g m m' u = inj₁ u







  inj₂MUaux : (g : Frame) (m m' : MethodsStruct)
                   (s  : SemiDec (λ g → methodsStruct2Method g m))
                   (s'  : SemiDec (λ g → methodsStruct2Method g m' ))
                   (u : methodsStruct2Method g m')
                   → methodsStruct2Methodaux g m m' s s'
  inj₂MUaux g m m' s (isEmpty x) u = ⊥-elim (x g u)
  inj₂MUaux g m m' (isEmpty x) posNonEmpty u = u
  inj₂MUaux g m m' posNonEmpty posNonEmpty u = inj₂ u

  inj₂MUoptimized : (g : Frame) (m m' : MethodsStruct)(u : methodsStruct2Method g m' )
                   → methodsStruct2Method g (m ⊎^ m') --isOpt
  inj₂MUoptimized g m m' u = inj₂MUaux g m m'
                         (methodsUnivIsEmpty  m)
                         (methodsUnivIsEmpty  m') u


  inj₂MUUnoptimized : (g : Frame) (m m' : MethodsStruct)(u : methodsStruct2Method g m' )
                   → methodsStruct2Method g (m ⊎^unoptimized m') --isOpt
  inj₂MUUnoptimized g m m' u = inj₂ u






  methodStruct : {c : Component}(e : ComponentEls c) → MethodsStruct
  methodStruct (add c'c x x₁ optimized) = methodStruct x  ⊎^ methodStruct x₁
  methodStruct (add c'c x x₁ notOptimized) = methodStruct x  ⊎^unoptimized methodStruct x₁
  methodStruct {atomicComp} (createC (button s)) = fficom
  methodStruct {atomicComp} (createC (txtbox s)) = ⊥^
  methodStruct _  = ⊥^

  methods : {c : Component}(e : ComponentEls c)(g : Frame) → Set
  methods e g =  methodsStruct2Method g (methodStruct e)



  methodsG : (g : Frame) → Set
  methodsG g =  methods g g


  methodLift : {c c'' : Component}(e : ComponentEls c)(e'₁ : ComponentEls c'')
               (g : Frame) (x : e <c e'₁)  (m : methods e g )
                → methods e'₁ g
  methodLift e .(add i e e₁ optimized) g (addsub i .e e₁ optimized) m =
                 inj₁MUoptimized g
                   (methodStruct e)
                   (methodStruct e₁)
                m
  methodLift e .(add i e e₁ notOptimzed) g (addsub i .e e₁ notOptimzed) m =
               inj₁MUUnoptimized g
                   (methodStruct e)
                   (methodStruct e₁)
                m

  methodLift e .(add i e'₂ e optimized) g (addlift i e'₂ .e optimized) m =
                 inj₂MUoptimized g
                    (methodStruct e'₂)
                    (methodStruct e)
                 m

  methodLift e .(add i e'₂ e notOptimzed) g (addlift i e'₂ .e notOptimzed) m =
                inj₂MUUnoptimized g
                    (methodStruct e'₂)
                    (methodStruct e)
                 m


  methodLift+ : {c c' : Component}(e : ComponentEls c)(e' : ComponentEls c')
                (g : Frame)(ee' : e <=c+ e')
                (m : methods e g)
                → methods e' g
  methodLift+ e .e g (in0= .e) m = m
  methodLift+ e e' g (in2= .e e'₁ .e' x ee'') m =
    methodLift+ e'₁ e' g ee'' (methodLift e e'₁ g x m)




data returnType (f : Frame) : Set where
    noChange           :  returnType f
    changedAttributes  :  properties f  →  returnType f
    changedGUI
      :  (fNew : Frame)  →  (properties fNew) → returnType f

nextStateFrame : (f : Frame)(r : returnType f) → Frame
nextStateFrame f noChange = f
nextStateFrame f (changedAttributes x) = f
nextStateFrame f (changedGUI fNew x) = fNew

handlerInterface : Interfaceˢ
handlerInterface .Stateˢ       = Frame
handlerInterface .Methodˢ f    = methodsG f
handlerInterface .Resultˢ f m  = returnType f
handlerInterface .nextˢ f m r  = nextStateFrame f r

HandlerObject : ∀ i → Frame → Set
HandlerObject i g =
  IOObjectˢ  GuiLev1Interface  handlerInterface i g

StateAndGuiObj : Set
StateAndGuiObj = Σ[ g ∈ Frame ] (properties g) × (HandlerObject ∞ g)

StateAndFFIComp : Set
StateAndFFIComp = Σ[ g ∈ Frame ] FFIcomponents g


--
-- Step 3 : create object of type HandlerObject
--

SingleMVar : {A : Set} → (mvar : MVar A) → VarList
SingleMVar {A} mvar = addVar mvar []


initHandlerMVar : (l : VarList) (g : Frame)
                     (a : properties g)
                     (f : HandlerObject ∞ g)
              → IOˢ GuiLev2Interface ∞
                    (λ s → Σ[ mvar ∈ MVar StateAndGuiObj ]
                    s ≡ addVar mvar l  ) l
initHandlerMVar l g a f = doˢ (createVar {_}{StateAndGuiObj} (g , a , f)) λ mvar →
                         returnˢ (mvar , refl)

initFFIMVar : (g : Frame)
              → (comp : (FFIcomponents g))
              → IOˢ GuiLev2Interface ∞
                    (λ s → Σ[ mvar ∈ MVar StateAndFFIComp ]
                    s ≡ SingleMVar mvar  ) []
initFFIMVar g comp = doˢ (createVar {_}{StateAndFFIComp} (g , comp)) λ mvar →
                        returnˢ (mvar , refl)



module _ where
  frameToEnclosing : (e : ComponentEls frame)(ffi : FFIcomponents e) → FFIFrame
  frameToEnclosing (createC x) ffi = ffi
  frameToEnclosing (add i e e₁ _) (proj₃ , proj₄) = frameToEnclosing e₁ proj₄


  componentToEnclosingIndex : (c : Component) → Set
  componentToEnclosingIndex frame = ⊥
  componentToEnclosingIndex atomicComp = ⊤

  componentToEnclosings : (c : Component)(i : componentToEnclosingIndex c) → Set
  componentToEnclosings frame ()
  componentToEnclosings atomicComp tt = FFIFrame


  createComp : {c : Component}{s : GuiLev2State}(e : ComponentEls c)
                    (enclosings : (i : componentToEnclosingIndex c) → componentToEnclosings c i)
                        → (existingFrame : Maybe FFIFrame) → IOₚˢ GuiLev2Interface ∞ (FFIcomponents e) s s



  createComp {frame} (createC fr) enc (just ffiFrame) = returnˢ (refl , ffiFrame)
  createComp {frame} (createC fr) enc nothing =
     doˢ (level1C createWxFrame) λ frFFI → returnˢ (refl , frFFI)

  createComp {frame} (add buttonFrame e frameEl _) enc maybeFr =
      createComp frameEl enc maybeFr >>=ₚˢ λ frameComp →
      createComp e (λ x → frameToEnclosing frameEl frameComp) maybeFr >>=ₚˢ λ buttonComp →
      returnˢ (refl , buttonComp , frameComp)
  createComp {atomicComp} (createC (button x)) enc maybeFr =
    doˢ (level1C (createButton (enc tt) x)) λ bt →
    returnˢ (refl , bt)

  createComp {atomicComp} (createC (txtbox x)) enc maybeFr =
    doˢ (level1C (createTextCtrl (enc tt) x)) λ txt →
    returnˢ (refl , txt)

  createComp {atomicComp} (add () e e₁ _) x y


  createFrame : (g : Frame) → IOₚˢ GuiLev2Interface ∞ (FFIcomponents g) [] []
  createFrame g = createComp {frame} g (λ x → ⊥-elim x) nothing

  reCreateFrame : {s : GuiLev2State}(g : Frame)(f : FFIFrame) → IOₚˢ GuiLev2Interface ∞ (FFIcomponents g) s s
  reCreateFrame g fr = createComp {frame} g (λ x → ⊥-elim x) (just fr)




module _ where
  ButtonComp : Set
  ButtonComp = ComponentEls atomicComp

  button2Frame : (bt  : ButtonComp)(g   : Frame)(ffi : FFIcomponents g)
               (rel : bt <=c+ g) → FFIFrame
  button2Frame bt g ffi (in2= {c' = frame} .bt .(add c'c bt e _) .g (addsub c'c .bt e _) rel) = ffiComponentsToFrame e (FFIcomponentsReduce+ e g aux ffi)
                       where
                            aux : e <=c+ g
                            aux = in2= e (add c'c bt e _) g (addlift c'c bt e _) rel
  button2Frame bt g ffi (in2= {c' = atomicComp} .bt .(add _ bt e _) .g (addsub () .bt e _) rel)
  button2Frame bt g ffi (in2= .bt .(add _ e'₁ bt _) .g (addlift {frame} () e'₁ .bt _) (in2= .(add _ e'₁ bt _) e' .g x rel))
  button2Frame bt g ffi (in2= .bt .(add _ e'₁ bt _) .g (addlift {atomicComp} () e'₁ .bt _) (in2= .(add _ e'₁ bt _) e' .g x rel))





  buttonHandleraux2 : ∀{i} → (bt  : ButtonComp)
                         (g   : Frame)
                         (ffi : FFIcomponents g)
                         (rel : bt <=c+ g)
                         (m   : methods bt g)
                         (a  : properties g)
                         (obj : HandlerObject ∞ g)
                         (r    : returnType g)
                         (obj' : IOObjectˢ GuiLev1Interface handlerInterface ∞
                                (nextStateFrame g r))
                         → IO GuiLev1Interface i StateAndGuiObj
  buttonHandleraux2 bt g ffi rel m a obj noChange obj' = return (g , a , obj')
  buttonHandleraux2 bt g ffi rel m a obj (changedAttributes a') obj' =
                    log "Changing Attributes Directly" λ _ →
                    return (g , a' , obj')
  buttonHandleraux2 (createC x) g ffi rel m a obj (changedGUI gNew a') obj' =
                    log "Firing GUI change ----> SEND FIRE" λ _ →
                    do (fireCustomEvent (button2Frame (createC x) g ffi rel)) λ _ →
                    return (gNew , a' , obj')


  buttonHandleraux2 (add () bt bt₁ _) g ffi rel m a obj (changedGUI gNew a') obj'


  buttonHandleraux : ∀{i} → (bt  : ButtonComp)
                         (g   : Frame)
                         (ffi : FFIcomponents g)
                         (rel : bt <=c+ g)
                         (m   : methods bt g)
                         (gNew  : Frame)
                         (a  : properties gNew)
                         (obj : HandlerObject ∞ gNew)
                         (dec : Dec (g ≡ gNew))
                         → IO GuiLev1Interface i StateAndGuiObj
  buttonHandleraux bt g ffi rel m .g a obj (Dec.yes refl)
               = method obj (methodLift+ bt g g  rel m) >>= λ { (r , obj') →
                 buttonHandleraux2 bt g ffi rel m a obj r obj'}
  buttonHandleraux bt g ffi rel m gNew a obj (Dec.no ¬p)
              = log "ERROR: button handler is called for wrong GUI !!" λ _ →
                return (gNew , a , obj)



  buttonHandler : ∀{i} → (bt  : ButtonComp)
                         (g   : Frame)
                         (ffi : FFIcomponents g)
                         (rel : bt <=c+ g)
                         (m   : methods bt g)
                         (obj : StateAndGuiObj)
                         → IO GuiLev1Interface i StateAndGuiObj
  buttonHandler {i} bt g ffi rel m (gNew , a , obj) = buttonHandleraux {i} bt g ffi rel m gNew a obj (g ≟Comp gNew)



  setHandler : ∀{i} → (c : Component)
                      (cels : ComponentEls c)
                      (g : Frame)
                      (ffiComp : FFIcomponents g)
                      (rel : cels <=c+ g)
                      (mvar : MVar StateAndGuiObj)
                      (restList : VarList)
                      → IOˢ GuiLev2Interface i (λ s' → s' ≡ addVar mvar restList  × Unit)
                                                (addVar mvar restList)


  setHandler .frame (add buttonFrame cels cels₁ _) g ffi rel mvar restList =
    setHandler frame cels₁ g ffi
                (in2= cels₁ (add buttonFrame cels cels₁ _) g (addlift buttonFrame cels cels₁ _) rel)
                mvar restList >>=ₚˢ λ r →
    setHandler atomicComp cels g ffi (in2= cels (add buttonFrame cels cels₁ _) g (addsub buttonFrame cels cels₁ _) rel)  mvar restList >>=ₚˢ λ r →
    returnˢ (refl , _)


  setHandler frame (createC tt) g ffi rel  mvar restList = returnˢ (refl , _)

  setHandler atomicComp (createC (button x)) g ffi (in2= .(createC (button x)) e' .g x₁ rel)  mvar restList =
     doˢ (setButtonHandler (FFIcomponentsReduce (createC (button x)) e' x₁
                              (FFIcomponentsReduce+ e' g rel ffi)  )

         [ (λ obj → buttonHandler (createC (button x)) g ffi
                      (in2= (createC (button x)) e' g x₁ rel) ffi (varListProj₁ restList obj)
                     >>= (λ { (g' , obj') → return (varListUpdateProj₁ restList  ( g' , obj') obj)}))]) λ _ →

     returnˢ (refl , _)


  setHandler atomicComp (createC (txtbox x)) g ffi (in2= .(createC (txtbox x)) e' .g x₁ rel)  mvar restList =      returnˢ (refl , _)

  setHandlerG : ∀{i} → (g : Frame)
                      (ffiComp : FFIcomponents g)
                      (mvar : MVar StateAndGuiObj)
                      (restList : VarList)
                      → IOˢ GuiLev2Interface i (λ s → s ≡ addVar mvar restList × Unit) (addVar mvar restList)
  setHandlerG g ffi mvar restList = setHandler frame g g ffi (in0= g) mvar restList



  deleteComp : {c : Component}{s : GuiLev2State}(e : ComponentEls c)(ffi : FFIcomponents e)
                          → IOₚˢ GuiLev2Interface ∞ Unit s s

  deleteComp {frame} (createC fr) _ = returnˢ (refl , _)

  deleteComp {frame} (add x be frameEl _) (ffi , ffis) =
    deleteComp be ffi >>=ₚˢ λ _ →
    deleteComp frameEl ffis >>=ₚˢ λ r →
    returnˢ (refl , _)

  deleteComp {atomicComp} (createC (button x)) ffiButton =
    doˢ (level1C (deleteButton ffiButton)) λ _ →
    returnˢ (refl , _)

  deleteComp {atomicComp} (createC (txtbox y)) ffiTextCtrl =
    doˢ (level1C (deleteTextCtrl ffiTextCtrl)) λ _ →
    returnˢ (refl , _)

  deleteComp {atomicComp} (add () a b _) y





  setAttributes : {c : Component}(i : Size)(e : ComponentEls c)(a : properties e)
                      (ffi : FFIcomponents e)
                          → IO GuiLev1Interface i ⊤


  setAttributes {frame} i (createC fr) (a , b , c , d) x =
    log " setting properties for Frame " λ _ →
    do (setChildredLayout x a b c d) λ _ →
    return tt

  setAttributes {frame} i (add x be frameEl _) (a , as) (ffi , ffis) =

    setAttributes i be a ffi >>= λ _ →
    setAttributes i frameEl as ffis >>= λ r →
    return tt

  setAttributes {atomicComp} i (createC (button x)) propColor ffiButton =
    do (setAttribButton ffiButton propColor) λ _ →
    return tt

  setAttributes {atomicComp} i (createC (txtbox y)) propColor ffiTextCtrl =
    do (setAttribTextCtrl ffiTextCtrl propColor) λ _ →
    return tt

  setAttributes {atomicComp} i (add () a b _) y z




getFrameGen : (g : Frame)(cp : FFIcomponents g) → FFIFrame
getFrameGen (createC x) cp = cp
getFrameGen (add buttonFrame g g₁ _) (compg , compg₁) = getFrameGen g₁ compg₁

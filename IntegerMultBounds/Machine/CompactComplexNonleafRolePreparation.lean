import IntegerMultBounds.Machine.CompactComplexNonleafRoleChildBank

/-! Shared child entry computes only its genuine row quotient. The stopped
branch consumes that source directly; only a true nonleaf branch splits the
already-quotiented child rows. There is no unconditional pre-guard split. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRolePreparation
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)
open CompactSpectatorLeafSetup (raw)
open CompactComplexNonleafRoleSplit (placement tapes)
variable {s c : ℕ}

private theorem quotient_valid (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hc : 0<c) :
    validSchedule (CompactComplexNonleafRoleSplit.quotientSchedule c) (raw sh rows ell p rho left count slots right src dst) := by
  simp [CompactComplexNonleafRoleSplit.quotientSchedule,validSchedule,valid,eval,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,
    ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    raw,hc]

private theorem quotient_eval (c : ℕ) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) :
    execute (CompactComplexNonleafRoleSplit.quotientSchedule c) (raw sh rows ell p rho left count slots right src dst)=
      raw sh (rows/c) ell p rho left count slots right src dst := by
  funext i
  fin_cases i <;> simp [CompactComplexNonleafRoleSplit.quotientSchedule,execute,eval,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,raw]

def quotientProgram (s c : ℕ) := Placement.placed
  (CompactNativeRoleOriginal.headerProgram c (CompactComplexNonleafRoleSplit.quotientSchedule c))
  (placement (s:=s) (c:=c))
def quotientCost (c : ℕ) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ) :=
  scheduleCost (CompactComplexNonleafRoleSplit.quotientSchedule c) (raw sh rows ell p rho left count slots right src dst)

def quotientOutput (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :=
  Placement.replace placement
    ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
      (SharedBank.empty 7 2))
    (CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))

/-- The selected current word moves through the physical Entry boundary and
gets a quotient header, while remaining the intact source for either branch. -/
theorem quotient_runs (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (hc : 0<c)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (quotientProgram s c)
      (fun z => z=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
        (SharedBank.empty 7 2))
      (fun z => z=quotientOutput selected sh rows ell p rho left count slots right src dst f v)
      (quotientCost c sh rows ell p rho left count slots right src dst) := by
  have hsource := CompactComplexNonleafRoleEntry.output_source selected sh rows ell p rho left count slots right src dst v
  have hi := CompactComplexNonleafRoleMerge.active_input
    (CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v)
    (raw sh rows ell p rho left count slots right src dst)
    (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) (fun _ _ => blank)
    (CompactComplexNonleafRoleEntry.output_headers selected sh rows ell p rho left count slots right src dst v)
    ⟨hsource.1,hsource.2.trans hf⟩
    (fun j => CompactComplexNonleafRoleEntry.output_roles_blank selected j sh rows ell p rho left count slots right src dst v)
  have hq := schedule_runs (a:=2) (CompactComplexNonleafRoleSplit.quotientSchedule c)
    (raw sh rows ell p rho left count slots right src dst)
    (quotient_valid c sh rows ell p rho left count slots right src dst hc)
  rw [quotient_eval] at hq
  have h := Placement.hoare_at
    (hoare_extend_eq hq (CompactNativeRoleInstall.blankRaw
      (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))) placement
    ((CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).append
      (SharedBank.empty 7 2)) hi
  exact h.consequence (fun _ h => h) (by rintro z ⟨w,rfl,rfl⟩; rfl) le_rfl

theorem quotient_output_active (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) :
    Placement.active placement (quotientOutput selected sh rows ell p rho left count slots right src dst f v)=
      CompactNativeRoleOriginal.bank (raw sh (rows/c) ell p rho left count slots right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c) :=
  Placement.active_replace _ _ _

open CompactComplexRecursiveGeometry
open CompactComplexChildHeadersData (parent child)
open RecursiveChildQuotientsConstant (bits)
variable {sh : Shape} {left k siteCount : ℕ}

def sourceReady (selected : Fin c) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2) :=
  let stage := parent rho visit hactive pair
  quotientOutput selected sh rows ell p stage.rho stage.left stage.f stage.slots stage.right
    stage.source.val stage.target.val f v

/-- A source-ready shared child entry follows the quotient-only boundary.
Both stopping-test outcomes still have the original intact selected source. -/
theorem child_entry_runs (selected : Fin c) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
        (sourceReady selected rho visit hactive pair rows ell p f v)=CompactComplexExponentStep.bank (k+2))
    (ht : (sourceReady selected rho visit hactive pair rows ell p f v).tape CompactComplexNonleafRoleChildBank.target=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : (sourceReady selected rho visit hactive pair rows ell p f v).head CompactComplexNonleafRoleChildBank.target=1)
    (hn : (sourceReady selected rho visit hactive pair rows ell p f v).tape CompactComplexNonleafRoleChildBank.current=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : (sourceReady selected rho visit hactive pair rows ell p f v).head CompactComplexNonleafRoleChildBank.current=1) :
    HoareTime (CompactComplexNonleafRoleChildBank.program (c:=c) headerStack pcStack liveStack site coordinate)
      (fun w => w=sourceReady selected rho visit hactive pair rows ell p f v)
      (fun w => w=CompactComplexNonleafRoleChildBank.output
        (sourceReady selected rho visit hactive pair rows ell p f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (CompactComplexNonleafRoleChildBank.cost siteCount parentTarget n (k+2)
        rho visit hactive pair coordinate (rows/c) ell p) := by
  apply CompactComplexNonleafRoleChildBank.runs _ parentTarget n (k+2) (by omega)
    headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p _ _ hx ht hh hn hp
  exact quotient_output_active selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val f v

def splitCurrentProgram (s c : ℕ) :=
  Placement.placed (CompactNativeRoleOriginal.splitProgram c) (placement (s:=10+s) (c:=c))

/-- Only the true nonleaf branch splits the current already-quotiented rows.
The source and original raw child metadata are the actual ChildBank endpoint. -/
theorem split_current_runs (w : Tapes (CompactComplexNonleafRoleChildBank.tapes s c) 2)
    (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    let bank := CompactComplexNonleafRoleChildBank.output w parentTarget n e headerStack pcStack liveStack site
      rho visit hactive pair coordinate rows ell p (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)
    let stage := child rho visit hactive pair coordinate
    HoareTime (splitCurrentProgram s c) (fun z => z=bank)
      (fun z => z=Placement.replace placement bank
        (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell p)
          (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
      (CompactNativeRoleOriginal.cost false (rows/c) c sh ell p stage.rho stage.left stage.f stage.slots stage.right
        stage.source.val stage.target.val) := by
  dsimp only
  let stage := child rho visit hactive pair coordinate
  have h0 := CompactNativeRoleReservedBridge.splits sh rows c ell p stage.rho stage.left stage.f stage.slots stage.right
    stage.source.val stage.target.val hc hr hd hG hA hK f hw
  have hi := CompactComplexNonleafRoleChildBank.output_active w parentTarget n e headerStack pcStack liveStack site
    rho visit hactive pair coordinate rows ell p (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)
  have h := Placement.hoare_at h0 placement
    (CompactComplexNonleafRoleChildBank.output w parentTarget n e headerStack pcStack liveStack site
      rho visit hactive pair coordinate rows ell p (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)) hi
  exact h.consequence (fun _ h => h) (by rintro z ⟨a,rfl,rfl⟩; rfl) le_rfl

/-- Actual descendant metadata gives the quotient and the next legal split;
no generated row dimensions are supplied as an independent premise. -/
theorem descendant_dimensions (c m d K j : ℕ) (hc : 0<c) (hK : 0<K)
    (hj : j+1<CompactGlobalRowPadding.depth m d) :
    CompactGlobalRowPadding.rowsAt c m d K j/c=CompactGlobalRowPadding.rowsAt c m d K (j+1) ∧
    0<CompactGlobalRowPadding.rowsAt c m d K j/c ∧
    c ∣ CompactGlobalRowPadding.rowsAt c m d K j/c :=
  ⟨CompactGlobalRowPadding.next_rows c m d K j,
    CompactComplexNonleafRoleSplit.descendant_divides c m d K j hc hK hj⟩

theorem split_current_descendant_runs (w : Tapes (CompactComplexNonleafRoleChildBank.tapes s c) 2)
    (parentTarget n e : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (m d K j ell p : ℕ) (hc : 0<c) (hK : 0<K)
    (hj : j+1<CompactGlobalRowPadding.depth m d)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hchunk : 0<sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh (CompactGlobalRowPadding.rowsAt c m d K j/c) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    let rows := CompactGlobalRowPadding.rowsAt c m d K j/c
    let hd := (descendant_dimensions c m d K j hc hK hj).2.2
    let bank := CompactComplexNonleafRoleChildBank.output w parentTarget n e headerStack pcStack liveStack site
      rho visit hactive pair coordinate rows ell p (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c)
    let stage := child rho visit hactive pair coordinate
    HoareTime (splitCurrentProgram s c) (fun z => z=bank)
      (fun z => z=Placement.replace placement bank
        (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw stage rows ell p)
          (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
      (CompactNativeRoleOriginal.cost false (rows/c) c sh ell p stage.rho stage.left stage.f stage.slots stage.right
        stage.source.val stage.target.val) :=
  split_current_runs w parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate _ ell p hc
    (descendant_dimensions c m d K j hc hK hj).2.1 (descendant_dimensions c m d K j hc hK hj).2.2
    hG hA hchunk f hw

theorem quotient_output_frame (selected : Fin c) (shape : Shape)
    (rows ell p rho lo count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array shape (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (i : Fin (tapes s c)) (hi : ∀ j,i≠CompactComplexNonleafRoleSplit.slot j) :
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).head i=
      ((CompactComplexNonleafRoleEntry.output selected shape rows ell p rho lo count slots right src dst v).append
        (SharedBank.empty 7 2)).head i ∧
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).tape i=
      ((CompactComplexNonleafRoleEntry.output selected shape rows ell p rho lo count slots right src dst v).append
        (SharedBank.empty 7 2)).tape i := by
  obtain ⟨i,rfl⟩ := (placement (s:=s) (c:=c)).surjective i
  induction i using Fin.addCases with
  | left i =>
    have he : placement (s:=s) (c:=c) (Fin.castAdd _ i)=CompactComplexNonleafRoleSplit.slot i := by
      simp [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (hi i he).elim
  | right i =>
    simp only [quotientOutput,Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

private theorem old_split_disjoint (j : Fin s) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (CompactComplexNonleafRoleReturnFrame.oldSlot (s:=s) (c:=c) j)≠
      CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [CompactComplexNonleafRoleReturnFrame.oldSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- The true live word, incoming parent target and all retained original
storage are proved directly from the parent caller before physical Entry. -/
theorem quotient_output_storage (selected : Fin c) (shape : Shape)
    (rows ell p rho lo count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array shape (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin s) :
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).head
        (Fin.castAdd 7 (CompactComplexNonleafRoleReturnFrame.oldSlot j))=
      v.head (CompactComplexNonleafRoleReturnFrame.oldSlot j) ∧
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).tape
        (Fin.castAdd 7 (CompactComplexNonleafRoleReturnFrame.oldSlot j))=
      v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot j) := by
  have h0 := quotient_output_frame selected shape rows ell p rho lo count slots right src dst f v
    (Fin.castAdd 7 (CompactComplexNonleafRoleReturnFrame.oldSlot j)) (old_split_disjoint j)
  have hj := CompactComplexNonleafRoleReturnFrame.old_slot_disjoint (s:=s) (c:=c) j
  have h1 := CompactComplexNonleafRoleEntry.output_frame selected shape rows ell p rho lo count slots right src dst v
    (CompactComplexNonleafRoleReturnFrame.oldSlot j) hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1
  constructor
  · exact h0.1.trans ((by simpa only [Tapes.append,Fin.addCases_left] using h1.1))
  · exact h0.2.trans ((by simpa only [Tapes.append,Fin.addCases_left] using h1.2))

def callerControl (i : Fin 43) : Fin (CompactComplexNonleafRoleEntry.tapes s c) :=
  Fin.castAdd 2 (Fin.castAdd c (CompactComplexControllerNativeFrame.controllerSlot (s:=s+43) i))

private theorem control_numeric (i j : Fin 43) : callerControl (s:=s) (c:=c) i≠CompactComplexNonleafRoleEntry.numeric j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [callerControl,CompactComplexControllerNativeFrame.controllerSlot,
    CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem control_source (i : Fin 43) : callerControl (s:=s) (c:=c) i≠CompactComplexNonleafRoleEntry.source := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [callerControl,CompactComplexControllerNativeFrame.controllerSlot,
    CompactComplexNonleafRoleEntry.source,CompactComplexSpectatorTargetBank.numericSlot,
    CompactComplexControllerNativeFrame.nativeSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem control_role (i : Fin 43) (j : Fin c) : callerControl (s:=s) i≠CompactComplexNonleafRoleEntry.roleTape j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [callerControl,CompactComplexControllerNativeFrame.controllerSlot,
    CompactComplexNonleafRoleEntry.roleTape,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem control_stack (i : Fin 43) : callerControl (s:=s) (c:=c) i≠CompactComplexNonleafRoleEntry.stack := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [callerControl,CompactComplexControllerNativeFrame.controllerSlot,
    CompactComplexNonleafRoleEntry.stack,CompactComplexNativeCodecFrame.permanentTapes,
    CompactComplexNativeRoleBridge.publicTapes,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem control_split (j : Fin 43) (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    Fin.castAdd 7 (callerControl (s:=s) (c:=c) j)≠CompactComplexNonleafRoleSplit.slot (s:=s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  simp only [callerControl,CompactComplexControllerNativeFrame.controllerSlot,Fin.val_castAdd] at hv
  have hi := i.isLt
  have hj := j.isLt
  unfold CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at hv
  unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount at hi
  split_ifs at hv <;> omega

/-- The actual control state and its blank arithmetic workspace are retained
from the original parent through payload Entry and the row quotient. -/
theorem quotient_output_control (selected : Fin c) (shape : Shape)
    (rows ell p rho lo count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array shape (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2) (j : Fin 43) :
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).head
        (Fin.castAdd 7 (callerControl j))=v.head (callerControl j) ∧
    (quotientOutput selected shape rows ell p rho lo count slots right src dst f v).tape
        (Fin.castAdd 7 (callerControl j))=v.tape (callerControl j) := by
  have h0 := quotient_output_frame selected shape rows ell p rho lo count slots right src dst f v
    (Fin.castAdd 7 (callerControl j)) (control_split j)
  have h1 := CompactComplexNonleafRoleEntry.output_frame selected shape rows ell p rho lo count slots right src dst v
    (callerControl j) (control_numeric j) (control_stack j) (control_source j) (control_role j)
  constructor
  · exact h0.1.trans ((by simpa only [Tapes.append,Fin.addCases_left] using h1.1))
  · exact h0.2.trans ((by simpa only [Tapes.append,Fin.addCases_left] using h1.2))

theorem source_ready_exponent (selected : Fin c) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2) :
    Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
        (sourceReady selected rho visit hactive pair rows ell p f v)=
      Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement (v.append (SharedBank.empty 7 2)) := by
  simp only [CompactComplexNonleafRoleChildBank.exponentPlacement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have h := quotient_output_control selected sh rows ell p
      (parent rho visit hactive pair).rho (parent rho visit hactive pair).left (parent rho visit hactive pair).f
      (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
      (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val f v (![1,28,29] i)
  · change (sourceReady selected rho visit hactive pair rows ell p f v).head
        (Fin.castAdd 7 (callerControl (![1,28,29] i))) =
      (v.append (SharedBank.empty 7 2)).head (Fin.castAdd 7 (callerControl (![1,28,29] i)))
    simpa only [sourceReady,Tapes.append,Fin.addCases_left] using h.1
  · change (sourceReady selected rho visit hactive pair rows ell p f v).tape
        (Fin.castAdd 7 (callerControl (![1,28,29] i))) =
      (v.append (SharedBank.empty 7 2)).tape (Fin.castAdd 7 (callerControl (![1,28,29] i)))
    simpa only [sourceReady,Tapes.append,Fin.addCases_left] using h.2

/-- Physical child entry derives its live, pending-target and exponent premises
from the actual original caller, rather than assuming a prepared child bank. -/
theorem child_entry_from_parent_runs (selected : Fin c) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      (v.append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1) :
    HoareTime (CompactComplexNonleafRoleChildBank.program (c:=c) headerStack pcStack liveStack site coordinate)
      (fun w => w=sourceReady selected rho visit hactive pair rows ell p f v)
      (fun w => w=CompactComplexNonleafRoleChildBank.output
        (sourceReady selected rho visit hactive pair rows ell p f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (CompactComplexNonleafRoleChildBank.cost siteCount parentTarget n (k+2)
        rho visit hactive pair coordinate (rows/c) ell p) := by
  have h8 := quotient_output_storage selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val f v ⟨8,by omega⟩
  have h7 := quotient_output_storage selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left (parent rho visit hactive pair).f
    (parent rho visit hactive pair).slots (parent rho visit hactive pair).right
    (parent rho visit hactive pair).source.val (parent rho visit hactive pair).target.val f v ⟨7,by omega⟩
  exact child_entry_runs selected rho visit hactive pair coordinate rows ell p f v parentTarget n
    headerStack pcStack liveStack site
    ((source_ready_exponent selected rho visit hactive pair rows ell p f v).trans hx)
    (h8.2.trans ht) (h8.1.trans hh) (h7.2.trans hn) (h7.1.trans hp)

def entryCost (s : ℕ) (selected : Fin c) (shape : Shape)
    (rows ell p rho lo count slots right src dst : ℕ) :=
  scheduleCost (CompactNativeRoleHeaders.schedule c false)
    (raw shape rows ell p rho lo count slots right src dst)+
    88*CompactComplexSpectatorVolumeHeaders.streamVolume shape c rows ell p false+
    scheduleCost CompactNativeRoleHeaders.cleanup
      (CompactNativeRoleHeaders.prepared c false shape rows ell p rho lo count slots right src dst)+2+
    (scheduleCost (CompactNativeRoleHeaders.schedule c true)
      (raw shape rows ell p rho lo count slots right src dst)+
      (88*(CompactComplexNonleafRoleEntry.inactive (s:=s) selected).length+88)*
        CompactComplexSpectatorVolumeHeaders.streamVolume shape c rows ell p true+
      scheduleCost CompactNativeRoleHeaders.cleanup
        (CompactNativeRoleHeaders.prepared c true shape rows ell p rho lo count slots right src dst)+2)+1

def childEntryProgram (selected : Fin c) (headerStack pcStack liveStack : Fin s)
    (site : Fin siteCount) (coordinate : Fin arity) :=
  seq (seq (extend (CompactComplexNonleafRoleEntry.program (s:=10+s) selected) 7)
      (quotientProgram (10+s) c))
    (CompactComplexNonleafRoleChildBank.program (c:=c) headerStack pcStack liveStack site coordinate)

/-- Complete literal parent-to-child entry: payload parking, row quotient and
child geometry saves run in order; both sequencing transitions are charged.
The intact selected source survives for the shared stopping guard. -/
theorem child_entry_from_caller_runs (selected : Fin c) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (coordinate : Fin arity)
    (rows ell p : ℕ) (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    (hx : Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      (v.append (SharedBank.empty 7 2))=CompactComplexExponentStep.bank (k+2))
    (ht : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits parentTarget))
    (hh : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1)
    (hn : v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=
      BinaryDescriptorStack.descriptor (bits n))
    (hp : v.head (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active CompactComplexNonleafRoleEntry.headerPlacement v=
      ActiveRepairRankHeadersCommands.bank
        (raw sh rows ell p (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val))
    (hclock : v.head CompactComplexNonleafRoleEntry.clock=0 ∧
      v.tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank))
    (hsource : v.head CompactComplexNonleafRoleEntry.source=0 ∧
      RoleArrayStack.Supported (v.tape CompactComplexNonleafRoleEntry.source)
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexNonleafRoleEntry.roleTape j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hf : v.tape (CompactComplexNonleafRoleEntry.roleTape selected)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f)) :
    HoareTime (childEntryProgram selected headerStack pcStack liveStack site coordinate)
      (fun w => w=v.append (SharedBank.empty 7 2))
      (fun w => w=CompactComplexNonleafRoleChildBank.output
        (sourceReady selected rho visit hactive pair rows ell p f v) parentTarget n (k+2)
        headerStack pcStack liveStack site rho visit hactive pair coordinate (rows/c) ell p
        (CompactNativeRoleReservedBridge.sourcePayload sh (rows/c) ell f c))
      (entryCost (10+s) selected sh rows ell p
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val+
        quotientCost c sh rows ell p
          (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
          (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
          (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
          (parent rho visit hactive pair).target.val+1+
        CompactComplexNonleafRoleChildBank.cost siteCount parentTarget n (k+2)
          rho visit hactive pair coordinate (rows/c) ell p+1) := by
  have he := CompactComplexNonleafRoleEntry.runs selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val v hc hr hgroup hG hA hK hraw hclock hsource hroles
  have hq := quotient_runs selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val hc f v hf
  have hh := child_entry_from_parent_runs selected rho visit hactive pair coordinate rows ell p f v
    parentTarget n headerStack pcStack liveStack site hx ht hh hn hp
  have h := ((hoare_extend_eq he (SharedBank.empty 7 2)).seq hq).seq hh
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    dsimp only [entryCost]
    omega)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRolePreparation

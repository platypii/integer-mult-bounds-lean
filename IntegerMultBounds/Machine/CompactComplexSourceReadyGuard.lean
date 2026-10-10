import IntegerMultBounds.Machine.CompactComplexNonleafRolePreparation
import IntegerMultBounds.Machine.CompactComplexControllerStopBranch

/-! The actual runtime stop decision on the unchanged Entry+7 bank. Seven
appended scratch tapes and three blank native-header scratch tapes form one
fixed stop10 workspace. Both branches reclaim all ten before touching the
intact selected source, raw geometry, live descriptors or controller stacks. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyGuard
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

abbrev permanent (s c : ℕ) := CompactComplexNonleafRoleEntry.tapes (10+s) c
abbrev tapes (s c : ℕ) := CompactComplexNonleafRoleChildBank.tapes s c

/-- Fixed borrowed stop workspace; it never includes the payload stack/clock. -/
def scratch (i : Fin 10) : Fin (tapes s c) :=
  if h : i.val<3 then Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric ⟨28+i.val,by omega⟩)
  else Fin.natAdd (permanent s c) ⟨i.val-3,by have hi := i.isLt; omega⟩

private theorem permanent_eq : permanent s c=165+s+c := by
  unfold permanent CompactComplexNonleafRoleEntry.tapes CompactComplexNativeCodecFrame.permanentTapes
    CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes
  omega

private theorem scratch_val (i : Fin 10) :
    (scratch (s:=s) (c:=c) i).val=if i.val<3 then 72+i.val else permanent s c+(i.val-3) := by
  unfold scratch
  split_ifs
  · simp [CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
      CompactComplexControllerNativeFrame.nativeSlot]
    omega
  · rfl

theorem scratch_injective : Function.Injective (scratch (s:=s) (c:=c)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [scratch_val,scratch_val,permanent_eq] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def placement := InjectivePlacement.placement (scratch (s:=s) (c:=c)) scratch_injective
  (by have h := permanent_eq (s:=s) (c:=c); change 10+(permanent s c+7-10)=permanent s c+7; omega)

@[simp] theorem placement_scratch (i : Fin 10) :
    placement (s:=s) (c:=c) (Fin.castAdd (tapes s c-10) i)=scratch i :=
  InjectivePlacement.active_slot _ _ _ _

def dimension : Fin (tapes s c) := Fin.castAdd 7 (CompactComplexNonleafRoleEntry.numeric 1)
def exponent : Fin (tapes s c) := CompactComplexNonleafRoleChildBank.control 1

private theorem dimension_scratch (i : Fin 10) : dimension (s:=s) (c:=c)≠scratch i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [dimension,Fin.val_castAdd,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_natAdd] at hv
  rw [scratch_val,permanent_eq] at hv
  split_ifs at hv <;> omega

private theorem exponent_scratch (i : Fin 10) : exponent (s:=s) (c:=c)≠scratch i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [exponent,CompactComplexNonleafRoleChildBank.control,Fin.val_mk] at hv
  rw [scratch_val,permanent_eq] at hv
  split_ifs at hv <;> omega

def Ready (v : Tapes (tapes s c) 2) : Prop :=
  ∀ i,v.head (scratch i)=0 ∧ v.tape (scratch i)=fun _ => blank

theorem ready_active (v : Tapes (tapes s c) 2) (h : Ready v) :
    Placement.active placement v=SharedBank.empty 10 2 := by
  apply congrArg₂ Tapes.mk <;> funext i
  · simpa only [placement_scratch] using (h i).1
  · simpa only [placement_scratch] using (h i).2

private def copyFocus (src : Fin (tapes s c)) (dst : Fin 10) := ![src,scratch dst]
private theorem copy_injective (src : Fin (tapes s c)) (dst : Fin 10) (hne : src≠scratch dst) :
    Function.Injective (copyFocus src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyFocus]

private def copyProgram (src : Fin (tapes s c)) (dst : Fin 10) (hne : src≠scratch dst) :=
  BinaryDescriptorCopyPlaced.program (a:=2) (copyFocus src dst) (copy_injective src dst hne)

private theorem copy_runs (v : Tapes (tapes s c) 2) (src : Fin (tapes s c)) (dst : Fin 10)
    (hne : src≠scratch dst) (n : ℕ)
    (hs : v.head src=1 ∧ v.tape src=RadixZeroFill.encodedBinary (bits n))
    (hd : v.head (scratch dst)=0 ∧ v.tape (scratch dst)=fun _ => blank) :
    HoareTime (copyProgram src dst hne) (fun w => w=v)
      (fun w => w=setTape v (scratch dst) (RadixZeroFill.encodedBinary (bits n)) 1)
      (2*(bits n).length+5) := by
  apply BinaryDescriptorCopyPlaced.copies v (copyFocus src dst) _ (bits n)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [copyFocus,Copy.cfg,hs.1,hs.2,hd.1,hd.2]

private theorem replace_twice (v : Tapes (tapes s c) 2) (old new : Tapes 10 2) :
    Placement.replace placement (Placement.replace placement v old) new=Placement.replace placement v new := by
  unfold Placement.replace
  rw [Placement.extra_combine]

private theorem update_small (v : Tapes (tapes s c) 2) (small : Tapes 10 2) (i : Fin 10)
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (Placement.replace placement v small) (scratch i) f p=
      Placement.replace placement v (setTape small i f p) := by
  rw [←placement_scratch,←PlacedDescriptorConstruction.replace_setTape,Placement.active_replace,replace_twice]

def initialized (v : Tapes (tapes s c) 2) (D e : ℕ) :=
  setTape (setTape v (scratch 6) (RadixZeroFill.encodedBinary (bits D)) 1)
    (scratch 9) (RadixZeroFill.encodedBinary (bits e)) 1

private theorem initialized_eq (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v) :
    initialized v D e=Placement.replace placement v (CompactComplexStopRun.input (bits D) (bits e)) := by
  have hv : v=Placement.replace placement v (SharedBank.empty 10 2) := by
    rw [←ready_active v h,Placement.replace_active]
  unfold initialized
  conv_lhs => rw [hv]
  rw [update_small,update_small]
  congr 1
  unfold CompactComplexStopRun.input CompactComplexStopRun.exponent FixedBasePowerUntil.input
  simp only [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def initializeProgram := seq
  (copyProgram (dimension (s:=s) (c:=c)) 6 (dimension_scratch 6))
  (copyProgram (exponent (s:=s) (c:=c)) 9 (exponent_scratch 9))

theorem initialize_runs (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v)
    (hd : v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head exponent=1 ∧ v.tape exponent=RadixZeroFill.encodedBinary (bits e)) :
    HoareTime initializeProgram (fun w => w=v) (fun w => w=initialized v D e)
      (2*(bits D).length+2*(bits e).length+11) := by
  have h0 := copy_runs v dimension 6 (dimension_scratch 6) D hd (h 6)
  have h69 : scratch (s:=s) (c:=c) 9≠scratch 6 := by
    intro h; have h' := scratch_injective h; cases h'
  have h1 := copy_runs (setTape v (scratch 6) (RadixZeroFill.encodedBinary (bits D)) 1)
    exponent 9 (exponent_scratch 9) e
    (by simpa only [setTape,Function.update_of_ne (exponent_scratch 6)] using he)
    (by simpa only [setTape,Function.update_of_ne h69] using h 9)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def computedFor (v : Tapes (tapes s c) 2) (B D e : ℕ) := Placement.replace placement v
  (CompactComplexStopRun.output B D (bits D) (bits e))
def computed (v : Tapes (tapes s c) 2) (D e : ℕ) := computedFor v CompactComplexStopThreshold.base D e

def setupProgramFor (B : ℕ) : Σ q,Program (tapes s c) q 2 := ⟨_,seq initializeProgram
  (Placement.placed (CompactComplexStopRun.program (q:=2) B) placement)⟩
def setupProgram : Σ q,Program (tapes s c) q 2 := setupProgramFor CompactComplexStopThreshold.base

def stopConstant := FixedBasePowerUntil.constant CompactComplexStopThreshold.base*
  CompactComplexStopThreshold.base+2*CompactComplexStopThreshold.base+27
def setupCostFor (B D e : ℕ) := 2*(bits D).length+2*(bits e).length+12+
  (FixedBasePowerUntil.constant B*B+2*B+27)*(D+e+1)
def setupCost (D e : ℕ) := setupCostFor CompactComplexStopThreshold.base D e

theorem setup_runsFor (B : ℕ) (hB : 2≤B) (v : Tapes (tapes s c) 2) (D e : ℕ) (hD : 0<D) (h : Ready v)
    (hd : v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head exponent=1 ∧ v.tape exponent=RadixZeroFill.encodedBinary (bits e)) :
    HoareTime (setupProgramFor B).2 (fun w => w=v) (fun w => w=computedFor v B D e) (setupCostFor B D e) := by
  have h0 := initialize_runs v D e h hd he
  have h1 := Placement.hoare_at
    (CompactComplexStopRun.runs_scalar B D hB hD (bits D) (bits e)
      (RecursiveChildQuotientsConstant.bits_value D) (RecursiveChildQuotientsConstant.bits_canonical D)
      (RecursiveChildQuotientsConstant.bits_canonical e)) placement (initialized v D e)
    (by rw [initialized_eq v D e h,Placement.active_replace])
  have h1' : HoareTime
      (Placement.placed (CompactComplexStopRun.program (q:=2) B) placement)
      (fun w => w=initialized v D e) (fun w => w=computedFor v B D e)
      ((FixedBasePowerUntil.constant B*B+2*B+27)*(D+e+1)) := by
    apply h1.consequence (fun _ h => h) _ (by
      simp only [RecursiveChildQuotientsConstant.bits_value]; exact le_rfl)
    rintro w ⟨small,rfl,rfl⟩
    rw [initialized_eq v D e h,replace_twice]
    rfl
  exact (h0.seq h1').consequence (fun _ h => h) (fun _ h => h) (by unfold setupCostFor; omega)

theorem setup_runs (v : Tapes (tapes s c) 2) (D e : ℕ) (hD : 0<D) (h : Ready v)
    (hd : v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head exponent=1 ∧ v.tape exponent=RadixZeroFill.encodedBinary (bits e)) :
    HoareTime setupProgram.2 (fun w => w=v) (fun w => w=computed v D e) (setupCost D e) :=
  setup_runsFor CompactComplexStopThreshold.base CompactComplexStopThreshold.base_ge_two v D e hD h hd he

def cleanupProgram : Program (tapes s c) 15 2 :=
  Placement.placed CompactComplexControllerStopCleanup.program placement
def cleanupCostFor (B D e : ℕ) := BinaryDescriptorCleanupList.cost CompactComplexControllerStopCleanup.descriptors
  (CompactComplexControllerStopCleanup.words B D e)+2
def cleanupCost (D e : ℕ) := cleanupCostFor CompactComplexStopThreshold.base D e

/-- All borrowed native scratch and appended scratch are reclaimed exactly. -/
theorem cleanup_runs (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v) :
    HoareTime cleanupProgram (fun w => w=computed v D e) (fun w => w=v) (cleanupCost D e) := by
  have hc := Placement.hoare_at (CompactComplexControllerStopCleanup.cleanup CompactComplexStopThreshold.base D e)
    placement (computed v D e) (Placement.active_replace _ _ _)
  apply hc.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  unfold computed computedFor
  rw [replace_twice,←ready_active v h,Placement.replace_active]

def test (sy : Fin (tapes s c) → Fin 6) : Bool := sy (scratch 8)==bitSymbol true

theorem flag (v : Tapes (tapes s c) 2) (D e : ℕ) :
    (computed v D e).reads (scratch 8)=bitSymbol (Networks.ComplexRecursiveCallSchema.stopped D e) := by
  unfold Tapes.reads computed computedFor
  rw [←placement_scratch]
  simp only [Placement.replace,Placement.combine_head_active,Placement.combine_tape_active]
  change (CompactComplexStopRun.output (q:=2) CompactComplexStopThreshold.base D (bits D) (bits e)).tape 8 0=_
  exact CompactComplexStopRun.flag_actual D e (bits D) (bits e) (RecursiveChildQuotientsConstant.bits_value e)

theorem decision (v : Tapes (tapes s c) 2) (D e : ℕ) :
    test (computed v D e).reads=Networks.ComplexRecursiveCallSchema.stopped D e := by
  unfold test
  rw [flag]
  cases Networks.ComplexRecursiveCallSchema.stopped D e <;> simp [bitSymbol]

def dispatch {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2) :=
  branch test (seq cleanupProgram leaf) (seq cleanupProgram recurse)

def program {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2) :=
  seq setupProgram.2 (dispatch leaf recurse)

private theorem clean_enters {q : ℕ} (next : Program (tapes s c) q 2)
    (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v) :
    ∃ n≤cleanupCost D e+1, run (seq cleanupProgram next) n
      ((computed v D e).start (seq cleanupProgram next))=
        some ((v.start next).mapState (Fin.natAdd 15)) := by
  obtain ⟨n,out,hn,hr,hh,hp⟩ := cleanup_runs v D e h (computed v D e) rfl
  have hz : run next 0 {state:=next.start,head:=out.head,tape:=out.tape}=some (v.start next) := by
    cases out
    cases hp
    rfl
  exact ⟨n+1,by omega,seq_run _ _ hr hh hz⟩

theorem dispatch_leaf_ready {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2)
    (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    ∃ n≤cleanupCost D e+2, run (dispatch leaf recurse) n ((computed v D e).start (dispatch leaf recurse))=
      some (((v.start leaf).mapState (Fin.natAdd 15)).mapState (leftState (15+q) (15+r))) := by
  obtain ⟨n,hn,hr⟩ := clean_enters leaf v D e h
  refine ⟨1+n,by omega,?_⟩
  unfold dispatch
  rw [run_add,run_one]
  rw [branch_step_enter_true test _ _ _ ((decision v D e).trans hs)]
  simp only [Option.bind_some]
  exact run_simulation _ _ (Config.mapState (leftState (15+q) (15+r)))
    (fun c d h => by rw [branch_step_left,h]; rfl) hr

theorem dispatch_recurse_ready {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2)
    (v : Tapes (tapes s c) 2) (D e : ℕ) (h : Ready v)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    ∃ n≤cleanupCost D e+2, run (dispatch leaf recurse) n ((computed v D e).start (dispatch leaf recurse))=
      some (((v.start recurse).mapState (Fin.natAdd 15)).mapState (rightState (15+q) (15+r))) := by
  obtain ⟨n,hn,hr⟩ := clean_enters recurse v D e h
  refine ⟨1+n,by omega,?_⟩
  unfold dispatch
  rw [run_add,run_one]
  rw [branch_step_enter_false test _ _ _ ((decision v D e).trans hs)]
  simp only [Option.bind_some]
  exact run_simulation _ _ (Config.mapState (rightState (15+q) (15+r)))
    (fun c d h => by rw [branch_step_right,h]; rfl) hr

private def activeIndex (i : Fin 10) : Fin (43+CompactNativeRoleInstall.rawCount c) :=
  if h : i.val<3 then Fin.castAdd _ ⟨28+i.val,by omega⟩
  else Fin.natAdd 43 ⟨1+c+(i.val-3),by
    have hi := i.isLt
    unfold CompactNativeRoleInstall.rawCount CompactNativeRoleDestructive.localCount
    omega⟩

private theorem activeIndex_slot (i : Fin 10) :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) (activeIndex i)=scratch i := by
  apply Fin.ext
  unfold activeIndex scratch
  split_ifs
  · have hfirst : 28+i.val<43 := by omega
    simp [CompactComplexNonleafRoleSplit.slot,hfirst,CompactComplexNonleafRoleEntry.numeric,
      CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot]
    omega
  · have h0 : ¬43+(1+c+(i.val-3))<43 := by omega
    have h2 : ¬43+(1+c+(i.val-3))<44+c := by omega
    simp [CompactComplexNonleafRoleSplit.slot,h0,h2]
    omega

/-- The actual raw native bank with its cleaned private suffix supplies all
ten guard scratch tapes; no separately prepared guard input is assumed. -/
theorem ready_of_active (v : Tapes (tapes s c) 2) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank st payload) : Ready v := by
  intro i
  have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.head (activeIndex i)) hi
  have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.tape (activeIndex i)) hi
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,activeIndex_slot] at hh ht
  by_cases hi : i.val<3
  · have h28 : ¬28+i.val<28 := by omega
    have h43 : 28+i.val<43 := by omega
    constructor
    · simpa [activeIndex,hi,h28,h43,CompactNativeRoleOriginal.bank,
        ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty,Fin.addCases] using hh
    · simpa [activeIndex,hi,h28,h43,CompactNativeRoleOriginal.bank,
        ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty,Fin.addCases] using ht
  · constructor
    · simpa [activeIndex,hi,CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,
        Tapes.append,SharedBank.empty,Fin.addCases] using hh
    · simpa [activeIndex,hi,CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,
        Tapes.append,SharedBank.empty,Fin.addCases] using ht

attribute [local irreducible] setupProgram setupProgramFor

private theorem dimension_slot :
    CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) (Fin.castAdd _ (1 : Fin 43))=
      dimension := by
  apply Fin.ext
  simp [CompactComplexNonleafRoleSplit.slot,dimension,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexControllerNativeFrame.nativeSlot]

/-- The runtime global dimension is read from the actual retained raw header. -/
theorem dimension_of_active (v : Tapes (tapes s c) 2) (sh : CompactGadgetReservationShape.Shape)
    (rows ell p rho left count slots right src dst : ℕ) (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst) payload) :
    v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits sh.axes) := by
  have hh := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.head (Fin.castAdd _ (1 : Fin 43))) hi
  have ht := congrArg (fun b : Tapes (43+CompactNativeRoleInstall.rawCount c) 2 => b.tape (Fin.castAdd _ (1 : Fin 43))) hi
  simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_bank,dimension_slot] at hh ht
  constructor
  · simpa [CompactNativeRoleOriginal.bank,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,CompactSpectatorLeafSetup.raw,Tapes.append,Fin.addCases] using hh
  · simpa [CompactNativeRoleOriginal.bank,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,CompactSpectatorLeafSetup.raw,Tapes.append,Fin.addCases] using ht

/-- Reservation stores the original global dimension `d`, not the retained
address dimension `D` or the residual active-axis count. -/
theorem original_dimension (m d D G K payload : ℕ) :
    (CompactGlobalReservation.shape c m d D G K payload).axes=d := rfl

/-- The actual multiplication parameter specialization stores `Sizes.d n`
unchanged through reservation and all recursive role-volume quotients. -/
theorem actual_dimension (n D payload : ℕ) :
    (CompactComplexRecursiveGeometry.actualShape n D payload).axes=Sizes.d n := rfl

theorem stopped_original (m d D G K payload e : ℕ) :
    Networks.ComplexRecursiveCallSchema.stopped
      (CompactGlobalReservation.shape c m d D G K payload).axes e=
      Networks.ComplexRecursiveCallSchema.stopped d e := rfl

theorem stopped_actual (n D payload e : ℕ) :
    Networks.ComplexRecursiveCallSchema.stopped
      (CompactComplexRecursiveGeometry.actualShape n D payload).axes e=
      Networks.ComplexRecursiveCallSchema.stopped (Sizes.d n) e := rfl

/-- Literal retained raw headers therefore supply precisely the manuscript's
original stopping dimension, without an extra equality premise. -/
theorem dimension_of_original (v : Tapes (tapes s c) 2)
    (m d D G K rows ell p rho left count slots right src dst : ℕ) (payload : Tapes (1+c) 2)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw (CompactReservationNativeRows.shape c m d D G K)
          rows ell p rho left count slots right src dst) payload) :
    v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits d) :=
  dimension_of_active v (CompactReservationNativeRows.shape c m d D G K)
    rows ell p rho left count slots right src dst payload hi

private theorem exponent_outside (i : Fin (43+CompactNativeRoleInstall.rawCount c)) :
    exponent (s:=s) (c:=c)≠CompactComplexNonleafRoleSplit.slot (s:=10+s) (c:=c) i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [exponent,CompactComplexNonleafRoleChildBank.control,Fin.val_mk] at hv
  dsimp only [CompactComplexNonleafRoleSplit.slot] at hv
  have hN := permanent_eq (s:=s) (c:=c)
  change CompactComplexNonleafRoleEntry.tapes (10+s) c=165+s+c at hN
  split_ifs at hv <;> omega

private theorem replace_exponent (v : Tapes (tapes s c) 2)
    (small : Tapes (43+CompactNativeRoleInstall.rawCount c) 2) :
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).head exponent=v.head exponent ∧
    (Placement.replace CompactComplexNonleafRoleSplit.placement v small).tape exponent=v.tape exponent := by
  obtain ⟨i,hi⟩ := (CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c)).surjective exponent
  rw [←hi]
  induction i using Fin.addCases with
  | left i =>
    have hs : CompactComplexNonleafRoleSplit.placement (s:=10+s) (c:=c) (Fin.castAdd _ i)=
        CompactComplexNonleafRoleSplit.slot i := by
      simp only [CompactComplexNonleafRoleSplit.placement,InjectivePlacement.active_slot]
    exact (exponent_outside i (hi.symm.trans hs)).elim
  | right i =>
    simp only [Placement.replace,Placement.combine_head_extra,Placement.combine_tape_extra,Placement.extra]
    trivial

/-- The exact child-entry endpoint provides scratch readiness and both runtime
test descriptors, including the physically decremented remaining exponent. -/
theorem child_output_ready (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (site : Fin siteCount)
    {sh : CompactGadgetReservationShape.Shape} {left k : ℕ}
    (rho : Fin sh.chunk) (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (coordinate : Fin CompactComplexRecursiveGeometry.arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    let bank := CompactComplexNonleafRoleChildBank.output v parentTarget n e headerStack pcStack liveStack site
      rho visit hactive pair coordinate rows ell p payload
    Ready bank ∧
      (bank.head dimension=1 ∧ bank.tape dimension=RadixZeroFill.encodedBinary (bits sh.axes)) ∧
      (bank.head exponent=1 ∧ bank.tape exponent=RadixZeroFill.encodedBinary (bits (e-1))) := by
  dsimp only
  have ha := CompactComplexNonleafRoleChildBank.output_active v parentTarget n e headerStack pcStack liveStack
    site rho visit hactive pair coordinate rows ell p payload
  refine ⟨ready_of_active _ _ payload ha,?_,?_⟩
  · exact dimension_of_active _ sh rows ell p
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).rho
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).left
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).f
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).slots
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).right
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).source.val
      (CompactComplexChildHeadersData.child rho visit hactive pair coordinate).target.val payload ha
  · unfold CompactComplexNonleafRoleChildBank.output CompactComplexNonleafRoleChildBank.coreOutput
    rw [(replace_exponent _ _).1,(replace_exponent _ _).2]
    simp [CompactComplexNonleafRoleChildBank.descended,exponent,setTape,
      BinaryDescriptorStackRoundtrip.descriptor_encoded]

theorem leaf_ready {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2)
    (v : Tapes (tapes s c) 2) (D e : ℕ) (hD : 0<D) (h : Ready v)
    (hd : v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head exponent=1 ∧ v.tape exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    ∃ n≤setupCost D e+cleanupCost D e+3, run (program leaf recurse) n (v.start (program leaf recurse))=
      some ((((v.start leaf).mapState (Fin.natAdd 15)).mapState
        (leftState (15+q) (15+r))).mapState (Fin.natAdd setupProgram.1)) := by
  obtain ⟨n,out,hn,hr,hh,hp⟩ := setup_runs v D e hD h hd he v rfl
  obtain ⟨m,hm,hs⟩ := dispatch_leaf_ready leaf recurse v D e h hs
  rw [←hp] at hs
  exact ⟨n+1+m,by omega,seq_run _ _ hr hh hs⟩

theorem recurse_ready {q r : ℕ} (leaf : Program (tapes s c) q 2) (recurse : Program (tapes s c) r 2)
    (v : Tapes (tapes s c) 2) (D e : ℕ) (hD : 0<D) (h : Ready v)
    (hd : v.head dimension=1 ∧ v.tape dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head exponent=1 ∧ v.tape exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    ∃ n≤setupCost D e+cleanupCost D e+3, run (program leaf recurse) n (v.start (program leaf recurse))=
      some ((((v.start recurse).mapState (Fin.natAdd 15)).mapState
        (rightState (15+q) (15+r))).mapState (Fin.natAdd setupProgram.1)) := by
  obtain ⟨n,out,hn,hr,hh,hp⟩ := setup_runs v D e hD h hd he v rfl
  obtain ⟨m,hm,hs⟩ := dispatch_recurse_ready leaf recurse v D e h hs
  rw [←hp] at hs
  exact ⟨n+1+m,by omega,seq_run _ _ hr hh hs⟩

def guardConstantFor (B : ℕ) := FixedBasePowerUntil.constant B*B+2*B+69
def guardConstant := guardConstantFor CompactComplexStopThreshold.base

theorem cost_linearFor (B D e : ℕ) (hB : 2≤B) :
    setupCostFor B D e+cleanupCostFor B D e+3≤guardConstantFor B*(D+e+1) := by
  have hd := ActiveRepairRankHeadersCommands.bits_length D
  have he := ActiveRepairRankHeadersCommands.bits_length e
  have hc := CompactComplexControllerStopCleanup.cost_le B D e hB
  unfold setupCostFor cleanupCostFor guardConstantFor
  nlinarith

theorem cost_linear (D e : ℕ) :
    setupCost D e+cleanupCost D e+3≤guardConstant*(D+e+1) :=
  cost_linearFor CompactComplexStopThreshold.base D e CompactComplexStopThreshold.base_ge_two

/-- The genuine parent visit and a positive current native row volume pay the
whole runtime test, branch transition and complete workspace cleanup. -/
theorem cost_native {sh : CompactGadgetReservationShape.Shape} {left k : ℕ}
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (rows ell p : ℕ) (hr : 0<rows) (hG : 0<sh.guard) :
    setupCost sh.axes (k+1)+cleanupCost sh.axes (k+1)+3≤
      (4*guardConstant)*CompactNativeRoleTransferBudget.volume rows sh ell p := by
  have hl := cost_linear sh.axes (k+1)
  have he := CompactComplexControllerChildBudget.exponent_bound visit hactive
  have hs : sh.axes+(k+1)+1≤(sh.axes+1)^2 := by nlinarith
  have hv := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=sh) rows ell p hr (by omega)
  have hm := Nat.mul_le_mul_left guardConstant (hs.trans hv)
  exact hl.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm] using hm)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyGuard

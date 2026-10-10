import IntegerMultBounds.Machine.CompactComplexControllerDenominatorTarget
import IntegerMultBounds.Machine.CompactComplexControllerStopCleanup
import IntegerMultBounds.Machine.Branch

/-! A fresh stop workspace follows the entire existing root bank, including
all its old stacks. The machine copies the real parent geometric exponent,
physically decrements only the copy, and computes the genuine child stop
flag. It then selects and constructs the child return target from actual
input-denominator and full-child-volume words, erasing all stop storage. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerChildStopTarget
noncomputable section
open CompactComplexControllerDenominator (size)
open CompactComplexControllerNativeFrame (controllerSlot nativeSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}
attribute [local irreducible] CompactComplexStopThreshold.base FixedBasePowerUntil.constant

abbrev total (s : ℕ) := size s+(10+0)
def bank (caller : Tapes (size s) 2) (stop : Tapes 10 2) : Tapes (total s) 2 :=
  ContiguousBankPlacement.bank caller stop (SharedBank.empty 0 2)
def stopSlot (i : Fin 10) : Fin (total s) := ContiguousBankPlacement.focus i
def dimensionSource : Fin (size s) := nativeSlot 1
def exponentSource : Fin (size s) := controllerSlot 1

def copySlots (src : Fin (size s)) (dst : Fin 10) : Fin 2 → Fin (total s) :=
  ![Fin.castAdd (10+0) src,stopSlot dst]
private theorem copy_injective (src : Fin (size s)) (dst : Fin 10) :
    Function.Injective (copySlots src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl |
    have hv := congrArg Fin.val h
    simp [copySlots,stopSlot,ContiguousBankPlacement.focus] at hv
    have hi := src.isLt
    omega
def copyProgram (src : Fin (size s)) (dst : Fin 10) :=
  BinaryDescriptorCopyPlaced.program (a:=2) (copySlots src dst) (copy_injective src dst)

private theorem update_stop (caller : Tapes (size s) 2) (stop : Tapes 10 2)
    (dst : Fin 10) (f : ℤ → Fin 6) (p : ℤ) :
    setTape (bank caller stop) (stopSlot dst) f p=bank caller (setTape stop dst f p) := by
  unfold bank ContiguousBankPlacement.bank stopSlot ContiguousBankPlacement.focus
  rw [SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

private theorem copy_runs (caller : Tapes (size s) 2) (stop : Tapes 10 2)
    (src : Fin (size s)) (dst : Fin 10) (value : ℕ)
    (ht : caller.tape src=RadixZeroFill.encodedBinary (bits value)) (hh : caller.head src=1)
    (hd : stop.tape dst=(fun _ => blank)) (hp : stop.head dst=0) :
    HoareTime (copyProgram src dst) (fun v => v=bank caller stop)
      (fun v => v=bank caller (setTape stop dst (RadixZeroFill.encodedBinary (bits value)) 1))
      (2*value+7) := by
  have h := BinaryDescriptorCopyPlaced.copies (bank caller stop) (copySlots src dst)
    (copy_injective src dst) (bits value) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
      all_goals simp [copySlots,bank,ContiguousBankPlacement.bank,stopSlot,
        ContiguousBankPlacement.focus,Tapes.append,Copy.cfg,ht,hh]
      · change (stop.append (SharedBank.empty 0 2)).head (Fin.castAdd 0 dst)=(0:ℤ)
        simpa only [Tapes.append,Fin.addCases_left] using hp
      · change (stop.append (SharedBank.empty 0 2)).tape (Fin.castAdd 0 dst)=(fun _ => blank)
        simpa only [Tapes.append,Fin.addCases_left] using hd)
  apply h.consequence (fun _ h => h) _ (by
    have hl := ActiveRepairRankHeadersCommands.bits_length value
    omega)
  rintro v rfl
  exact update_stop caller stop dst _ _

def initialized (D e : ℕ) : Tapes 10 2 :=
  setTape (setTape (SharedBank.empty 10 2) 6 (RadixZeroFill.encodedBinary (bits D)) 1)
    9 (RadixZeroFill.encodedBinary (bits e)) 1
private theorem initialized_eq (D e : ℕ) :
    initialized D e=CompactComplexStopRun.input (bits D) (bits e) := by
  unfold initialized CompactComplexStopRun.input CompactComplexStopRun.exponent FixedBasePowerUntil.input
  simp only [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def initializeProgram := seq (copyProgram (dimensionSource (s:=s)) 6)
  (copyProgram exponentSource 9)
theorem initialize_runs (caller : Tapes (size s) 2) (D e : ℕ)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1) :
    HoareTime initializeProgram (fun v => v=bank caller (SharedBank.empty 10 2))
      (fun v => v=bank caller (CompactComplexStopRun.input (bits D) (bits e)))
      (2*D+2*e+16) := by
  have h0 := copy_runs caller (SharedBank.empty 10 2) dimensionSource 6 D hd hhd rfl rfl
  have h1 := copy_runs caller
    (setTape (SharedBank.empty 10 2) 6 (RadixZeroFill.encodedBinary (bits D)) 1)
    exponentSource 9 e he hhe (by simp [setTape,SharedBank.empty])
      (by simp [setTape,SharedBank.empty])
  have h := h0.seq h1
  change HoareTime initializeProgram _ (fun v => v=bank caller (initialized D e)) _ at h
  rw [initialized_eq] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

def decrementSlots : Fin 3 → Fin 10 := ![9,0,1]
private theorem decrement_injective : Function.Injective decrementSlots := by decide
def decrementPlacement : Fin (3+7) ≃ Fin 10 :=
  InjectivePlacement.placement decrementSlots decrement_injective rfl
def decrementProgram := Placement.placed (CompactComplexExponentStep.program (a:=2)) decrementPlacement
theorem decrement_runs (D e : ℕ) (he : 0<e) :
    HoareTime decrementProgram
      (fun v => v=CompactComplexStopRun.input (bits D) (bits e))
      (fun v => v=CompactComplexStopRun.input (bits D) (bits (e-1)))
      (20*(e+1)+100) := by
  have h := CompactComplexExponentStep.runs_at decrementPlacement
    (CompactComplexStopRun.input (q:=2) (bits D) (bits e)) e he (by
      apply congrArg₂ Tapes.mk <;> funext i
      all_goals simp only [decrementPlacement,InjectivePlacement.active_slot]
      all_goals fin_cases i <;> rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  simp only [decrementPlacement,InjectivePlacement.active_slot,decrementSlots,Matrix.cons_val_zero]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def stopConstantFor (B : ℕ) := FixedBasePowerUntil.constant B*B+2*B+27
def prepareCostFor (B D e : ℕ) := 2*D+2*e+16+20*(e+1)+100+stopConstantFor B*(D+(e-1)+1)+2
def prepareProgramFor (B : ℕ) := seq (initializeProgram (s:=s))
  (ContiguousBankPlacement.program (l:=size s) (r:=0)
    (seq decrementProgram (CompactComplexStopRun.program (q:=2) B)))

/-- The stop exponent is physically decremented from the copied parent
descriptor. Neither the child exponent word nor the decision is supplied. -/
theorem prepare_runsFor (B : ℕ) (hB : 2≤B) (caller : Tapes (size s) 2)
    (D e : ℕ) (hD : 0<D) (hepos : 0<e)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1) :
    HoareTime (prepareProgramFor B) (fun v => v=bank caller (SharedBank.empty 10 2))
      (fun v => v=bank caller (CompactComplexStopRun.output B D
        (bits D) (bits (e-1)))) (prepareCostFor B D e) := by
  have h0 := initialize_runs caller D e hd hhd he hhe
  have hstop := CompactComplexStopRun.runs_scalar (q:=2) B D hB hD (bits D) (bits (e-1))
    (RecursiveChildQuotientsConstant.bits_value D) (RecursiveChildQuotientsConstant.bits_canonical D)
    (RecursiveChildQuotientsConstant.bits_canonical (e-1))
  simp only [RecursiveChildQuotientsConstant.bits_value] at hstop
  have h1 := ContiguousBankPlacement.runs ((decrement_runs D e hepos).seq hstop)
    caller (SharedBank.empty 0 2)
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
  unfold prepareCostFor stopConstantFor
  omega

def prepareCost (D e : ℕ) := prepareCostFor CompactComplexStopThreshold.base D e
def prepareProgram := prepareProgramFor (s:=s) CompactComplexStopThreshold.base
theorem prepare_runs (caller : Tapes (size s) 2) (D e : ℕ) (hD : 0<D) (hepos : 0<e)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1) :
    HoareTime prepareProgram (fun v => v=bank caller (SharedBank.empty 10 2))
      (fun v => v=bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
        (bits D) (bits (e-1)))) (prepareCost D e) :=
  prepare_runsFor CompactComplexStopThreshold.base CompactComplexStopThreshold.base_ge_two
    caller D e hD hepos hd hhd he hhe

def test (symbols : Fin (total s) → Fin 6) : Bool :=
  symbols (stopSlot 8)==bitSymbol true
def chosenTarget (D childExponent n fullVolume : ℕ) :=
  if Networks.ComplexRecursiveCallSchema.stopped D childExponent then n+fullVolume else n+2*fullVolume

theorem decision (caller : Tapes (size s) 2) (D childExponent : ℕ) :
    test (bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
      (bits D) (bits childExponent))).reads=
        Networks.ComplexRecursiveCallSchema.stopped D childExponent := by
  unfold test
  simp only [bank,ContiguousBankPlacement.bank,stopSlot,ContiguousBankPlacement.focus,
    Tapes.reads,Tapes.append,Fin.addCases_right,Fin.addCases_left]
  change ((CompactComplexStopRun.output (q:=2) CompactComplexStopThreshold.base D
    (bits D) (bits childExponent)).tape 8 0==bitSymbol true)=
      Networks.ComplexRecursiveCallSchema.stopped D childExponent
  rw [CompactComplexStopRun.flag_actual D childExponent _ _
    (RecursiveChildQuotientsConstant.bits_value childExponent)]
  cases Networks.ComplexRecursiveCallSchema.stopped D childExponent <;> rfl

def cleanupCost (D childExponent : ℕ) := 4*D+2*childExponent+23
def cleanupProgram := ContiguousBankPlacement.program (l:=size s) (r:=0)
  (CompactComplexControllerStopCleanup.program (a:=2))
private theorem cleanup_runs (caller : Tapes (size s) 2) (D childExponent : ℕ) :
    HoareTime cleanupProgram
      (fun v => v=bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
        (bits D) (bits childExponent)))
      (fun v => v=bank caller (SharedBank.empty 10 2)) (cleanupCost D childExponent) := by
  have h := (CompactComplexControllerStopCleanup.cleanup (a:=2)
    CompactComplexStopThreshold.base D childExponent).consequence (fun _ h => h) (fun _ h => h)
      (CompactComplexControllerStopCleanup.cost_le CompactComplexStopThreshold.base D childExponent
        CompactComplexStopThreshold.base_ge_two)
  exact ContiguousBankPlacement.runs h caller (SharedBank.empty 0 2)

def leafBody := seq (cleanupProgram (s:=s))
  (extend (CompactComplexControllerDenominatorTarget.leafProgram (s:=s)) 10)
def networkBody := seq (cleanupProgram (s:=s))
  (extend (CompactComplexControllerDenominatorTarget.networkProgram (s:=s)) 10)
def branchProgram := branch (test (s:=s)) leafBody networkBody

private theorem leaf_body_runs (caller : Tapes (size s) 2) (D childExponent n fullVolume : ℕ)
    (ha : Placement.active CompactComplexControllerDenominatorTarget.placement caller=
      CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime leafBody
      (fun v => v=bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
        (bits D) (bits childExponent)))
      (fun v => v=bank (CompactComplexControllerDenominatorTarget.installed caller (n+fullVolume))
        (SharedBank.empty 10 2))
      (cleanupCost D childExponent+1+CompactNativeDenominatorTarget.leafCost n fullVolume) := by
  have h := hoare_extend_eq (CompactComplexControllerDenominatorTarget.leaf_runs caller n fullVolume ha)
    ((SharedBank.empty 10 2).append (SharedBank.empty 0 2))
  exact (cleanup_runs caller D childExponent).seq h

private theorem network_body_runs (caller : Tapes (size s) 2) (D childExponent n fullVolume : ℕ)
    (ha : Placement.active CompactComplexControllerDenominatorTarget.placement caller=
      CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime networkBody
      (fun v => v=bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
        (bits D) (bits childExponent)))
      (fun v => v=bank (CompactComplexControllerDenominatorTarget.installed caller (n+2*fullVolume))
        (SharedBank.empty 10 2))
      (cleanupCost D childExponent+1+CompactNativeDenominatorTarget.networkCost n fullVolume) := by
  have h := hoare_extend_eq (CompactComplexControllerDenominatorTarget.network_runs caller n fullVolume ha)
    ((SharedBank.empty 10 2).append (SharedBank.empty 0 2))
  exact (cleanup_runs caller D childExponent).seq h

/-- A real symbol test selects the constructor. Its output policy uses the
proved actual stop flag, while every copied stop descriptor is reclaimed. -/
theorem branch_runs (caller : Tapes (size s) 2) (D childExponent n fullVolume : ℕ)
    (ha : Placement.active CompactComplexControllerDenominatorTarget.placement caller=
      CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime branchProgram
      (fun v => v=bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
        (bits D) (bits childExponent)))
      (fun v => v=bank (CompactComplexControllerDenominatorTarget.installed caller
        (chosenTarget D childExponent n fullVolume)) (SharedBank.empty 10 2))
      (cleanupCost D childExponent+max (CompactNativeDenominatorTarget.leafCost n fullVolume)
        (CompactNativeDenominatorTarget.networkCost n fullVolume)+2) := by
  let before := bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D
    (bits D) (bits childExponent))
  let after := bank (CompactComplexControllerDenominatorTarget.installed caller
    (chosenTarget D childExponent n fullVolume)) (SharedBank.empty 10 2)
  have hM : HoareTime leafBody (fun v => v=before ∧ test v.reads=true) (fun v => v=after)
      (cleanupCost D childExponent+1+CompactNativeDenominatorTarget.leafCost n fullVolume) := by
    rintro v ⟨rfl,hflag⟩
    have hs := (decision caller D childExponent).symm.trans hflag
    obtain ⟨k,c,hk,hr,hh,hp⟩ := leaf_body_runs caller D childExponent n fullVolume ha before rfl
    exact ⟨k,c,hk,hr,hh,by simpa [after,chosenTarget,hs] using hp⟩
  have hN : HoareTime networkBody (fun v => v=before ∧ test v.reads=false) (fun v => v=after)
      (cleanupCost D childExponent+1+CompactNativeDenominatorTarget.networkCost n fullVolume) := by
    rintro v ⟨rfl,hflag⟩
    have hs := (decision caller D childExponent).symm.trans hflag
    obtain ⟨k,c,hk,hr,hh,hp⟩ := network_body_runs caller D childExponent n fullVolume ha before rfl
    exact ⟨k,c,hk,hr,hh,by simpa [after,chosenTarget,hs] using hp⟩
  exact (branch_hoare test hM hN).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program := seq (prepareProgram (s:=s)) branchProgram
def costFor (B D e n fullVolume : ℕ) := prepareCostFor B D e+cleanupCost D (e-1)+
  max (CompactNativeDenominatorTarget.leafCost n fullVolume)
    (CompactNativeDenominatorTarget.networkCost n fullVolume)+3
def cost (D e n fullVolume : ℕ) := costFor CompactComplexStopThreshold.base D e n fullVolume
private theorem paid_join (A B C : ℕ) : A+1+(B+C+2)≤A+B+C+3 := by omega

/-- End-to-end child-target preparation from genuine original headers and
blank appended storage, with runtime choice and all cleanup charged. -/
theorem runs (caller : Tapes (size s) 2) (D e n fullVolume : ℕ) (hD : 0<D) (hepos : 0<e)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1)
    (ha : Placement.active CompactComplexControllerDenominatorTarget.placement caller=
      CompactNativeDenominatorTarget.input n fullVolume) :
    HoareTime program (fun v => v=bank caller (SharedBank.empty 10 2))
      (fun v => v=bank (CompactComplexControllerDenominatorTarget.installed caller
        (chosenTarget D (e-1) n fullVolume)) (SharedBank.empty 10 2)) (cost D e n fullVolume) := by
  have h0 := prepare_runs caller D e hD hepos hd hhd he hhe
  have h1 := branch_runs caller D (e-1) n fullVolume ha
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (paid_join _ _ _)

def timeConstantFor (B : ℕ) := stopConstantFor B+247
@[irreducible] def timeConstant := timeConstantFor CompactComplexStopThreshold.base
private theorem fixed_allowance (C D e n v A : ℕ)
    (hA : A≤C*(D+e+1)+6*D+24*e+6*n+36*v+247) :
    A≤(C+247)*(D+e+n+v+1) := by
  have hm := Nat.mul_le_mul_left C (show D+e+1≤D+e+n+v+1 by omega)
  nlinarith

/-- All stop computation, copied-exponent decrement, real branch selection,
target construction and cleanup have a single input-independent constant. -/
theorem cost_leFor (B D e n fullVolume : ℕ) :
    costFor B D e n fullVolume≤timeConstantFor B*(D+e+n+fullVolume+1) := by
  have hl := CompactComplexControllerDenominatorTarget.leaf_cost_le n fullVolume
  have hn := CompactComplexControllerDenominatorTarget.network_cost_le n fullVolume
  have hm : max (CompactNativeDenominatorTarget.leafCost n fullVolume)
      (CompactNativeDenominatorTarget.networkCost n fullVolume)≤6*n+36*fullVolume+83 :=
    max_le (hl.trans (by omega)) hn
  have hp : e-1≤e := Nat.sub_le e 1
  have hc := Nat.mul_le_mul_left (stopConstantFor B)
    (show D+(e-1)+1≤D+e+1 by omega)
  unfold timeConstantFor
  apply fixed_allowance
  unfold costFor prepareCostFor cleanupCost
  omega

theorem cost_le (D e n fullVolume : ℕ) :
    cost D e n fullVolume≤timeConstant*(D+e+n+fullVolume+1) := by
  unfold cost timeConstant
  exact cost_leFor CompactComplexStopThreshold.base D e n fullVolume

open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open CompactComplexControllerDenominatorTarget (parentBank)

theorem chosen_policy (D k n : ℕ) :
    chosenTarget D (k+1) n (arity^(k+1))=
      if Networks.ComplexRecursiveCallSchema.stopped D (k+1) then
        CompactComplexDenominatorPolicy.leafTarget n (k+1)
      else CompactComplexDenominatorPolicy.networkTarget n k := rfl

theorem parent_dimension {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 23 2)
    (storage : Tapes (10+s) 2) :
    (parentBank rho visit hactive pair rows control queue tail storage).tape dimensionSource=
      RadixZeroFill.encodedBinary (bits sh.axes) ∧
    (parentBank rho visit hactive pair rows control queue tail storage).head dimensionSource=1 :=
  ⟨rfl,rfl⟩

theorem parent_exponent {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (st : ActiveRepairRankHeadersCommands.State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (10+s) 2) :
    (parentBank rho visit hactive pair rows (ActiveRepairRankHeadersCommands.bank st) queue tail storage).tape
        exponentSource=RadixZeroFill.encodedBinary (bits (k+2)) ∧
    (parentBank rho visit hactive pair rows (ActiveRepairRankHeadersCommands.bank st) queue tail storage).head
        exponentSource=1 := by
  simp only [parentBank,CompactComplexControllerNativeFrame.bank,exponentSource,controllerSlot,
    Tapes.append,Fin.addCases_left]
  constructor
  · change (match st 1 with | none => fun _ => blank | some e => RadixZeroFill.encodedBinary (bits e))=_
    rw [h1]
  · change (if (st 1).isSome then (1:ℤ) else 0)=1
    rw [h1]
    rfl

/-- Actual child entry uses the real shape dimension, parent exponent and
retained native child-volume header. The machine itself derives and selects
the certified branch policy; no stopping hypothesis is a theorem premise. -/
theorem parent_runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows : ℕ)
    (st : ActiveRepairRankHeadersCommands.State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (10+s) 2) (n : ℕ)
    (hn : storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) ∧
      storage.head ⟨7,by omega⟩=1)
    (ht : storage.tape ⟨8,by omega⟩=(fun _ => blank) ∧ storage.head ⟨8,by omega⟩=0)
    (hw : storage.tape ⟨0,by omega⟩=(fun _ => blank) ∧ storage.head ⟨0,by omega⟩=0) :
    let caller := parentBank rho visit hactive pair rows (ActiveRepairRankHeadersCommands.bank st)
      queue tail storage
    HoareTime program (fun v => v=bank caller (SharedBank.empty 10 2))
      (fun v => v=bank (CompactComplexControllerDenominatorTarget.installed caller
        (if Networks.ComplexRecursiveCallSchema.stopped sh.axes (k+1) then
          CompactComplexDenominatorPolicy.leafTarget n (k+1)
        else CompactComplexDenominatorPolicy.networkTarget n k)) (SharedBank.empty 10 2))
      (cost sh.axes (k+2) n (arity^(k+1))) := by
  dsimp only
  have hd := parent_dimension rho visit hactive pair rows (ActiveRepairRankHeadersCommands.bank st)
    queue tail storage
  have he := parent_exponent rho visit hactive pair rows st h1 queue tail storage
  have ha := CompactComplexControllerDenominatorTarget.active_parent rho visit hactive pair rows
    (ActiveRepairRankHeadersCommands.bank st) queue tail storage n hn ht hw
  have hpow : 0<arity^(k+2) := pow_pos (by decide) _
  have hfit := visit.fits
  have hD : 0<sh.axes := by omega
  have h := runs _ sh.axes (k+2) n (arity^(k+1)) hD (by omega) hd.1 hd.2 he.1 he.2 ha
  rw [show k+2-1=k+1 by omega,chosen_policy] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexControllerChildStopTarget

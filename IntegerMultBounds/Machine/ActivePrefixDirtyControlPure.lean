import IntegerMultBounds.Machine.ActivePrefixDirtyControlPureCleanup
import IntegerMultBounds.Machine.ActivePrefixDirtyControl

/-! The second dirty-U controlled early load emits pure target parity. It uses
the same real source/clock setup and cleanup, with a target-only Boolean gather. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPure
noncomputable section
open ActivePrefixDirtyControlData hiding offsetWord gathered offset_length
open ActivePrefixDirtyControlPureBank
open ActivePrefixDirtyControlHeaders (bank)
variable {a : ℕ}

def gather := extend (BinaryVaryingParityOnlyPlaced.program (a := a) gatherFocus (by decide)) 4
def prepare := seq (seq (seq (seq (ActivePrefixDirtyControlHeaders.program (a := a))
  (ActivePrefixDirtyControlRun.projectT .parity)) ActivePrefixDirtyControlRun.projectU)
  ActivePrefixDirtyControlRun.projectClock) ActivePrefixDirtyControlRun.extract
def program := seq (seq (prepare (a := a)) gather) ActivePrefixDirtyControlPureCleanup.program

def input (hs : Fin 6 → List Bool) := ActivePrefixDirtyControl.input (a := a) hs
def output (s : Shape .parity) (hs : Fin 6 → List Bool) := bank (ActivePrefixDirtyControlPureCleanup.result (a := a) s hs)

theorem gather_runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (gather (a := a)) (fun v => v=bank (controlReady s hs)) (fun v => v=bank (gathered s hs))
      (320*(((controlWord s).length+1)*(s.q+s.b+1))) := by
  obtain ⟨ht,hx,hz⟩ := ActivePrefixDirtyControlBank.gather_tapes (a := a) s hs
  obtain ⟨hh,hp,hr,ho⟩ := ActivePrefixDirtyControlBank.gather_heads (a := a) s hs
  have h := BinaryVaryingParityOnlyPlaced.runs (controlReady (a := a) s hs) gatherFocus (by decide)
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 (gatherHeaders s hs)
    (by intro i; fin_cases i; exact hv 3; exact hv 4
        change Counter.value (RecursiveChildQuotientsConstant.bits (s.n*2^s.W))=(controlWord s).length
        rw [RecursiveChildQuotientsConstant.bits_value,control_length,Nat.mul_comm])
    (by intro i; fin_cases i; exact hc 3; exact hc 4; exact RecursiveChildQuotientsConstant.bits_canonical _)
    ht hh (by simp [tempWord,tempWidth,Nat.mul_assoc,BinaryVaryingOffsetGatherPlaced.sourceWidth]) hx hz hp hr ho
  simpa only [gather,BinaryVaryingParityOnlyPlaced.input,ActivePrefixDirtyControlRun.pad20,gathered]
    using hoare_extend_eq h (SharedBank.empty 4 a)

theorem cleanupCost_eq (s : Shape .parity) :
    ActivePrefixDirtyControlPureCleanup.cost s=ActivePrefixDirtyControlCleanup.cost s := by
  unfold ActivePrefixDirtyControlPureCleanup.cost ActivePrefixDirtyControlCleanup.cost
  rw [offset_length,ActivePrefixDirtyControlData.offset_length]

theorem runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input hs) (fun v => v=output s hs)
      (ActivePrefixDirtyControl.cost s) := by
  have h := ((((((ActivePrefixDirtyControlHeaders.runs (a := a) s hs hv hc).seq
    (ActivePrefixDirtyControlRun.projectT_runs s hs hv hc)).seq
    (ActivePrefixDirtyControlRun.projectU_runs s hs hv hc)).seq
    (ActivePrefixDirtyControlRun.projectClock_runs s hs hv hc)).seq
    (ActivePrefixDirtyControlRun.extract_runs s hs hv hc)).seq
    (gather_runs s hs hv hc)).seq (ActivePrefixDirtyControlPureCleanup.runs s hs)
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (by rw [cleanupCost_eq]; unfold ActivePrefixDirtyControl.cost ActivePrefixDirtyControlRun.cost; omega)

theorem runs_linear (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=input hs) (fun v => v=output s hs)
      (ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s) :=
  (runs s hs hv hc).consequence (fun _ h => h) (fun _ h => h) (ActivePrefixDirtyControl.cost_bound s)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlPure

import IntegerMultBounds.Machine.CompactSpectatorLeafAxis
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! A literal counted leaf interval over the immutable global coefficient word.
Every axis body is proved by native execution, the actual count is read from
the retained width header, and all loop and leaf-local numeric tapes are erased. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafLoop
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorLeafHeaders (initial)
variable (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)

def run : ℕ → Array s rows ell → Array s rows ell
  | 0,f => f
  | n+1,f => if hi : n<arity^k then CompactSpectatorLeafAxis.result s rows ell p rho visit ⟨n,hi⟩
      (run n f) else run n f

theorem width_run (n : ℕ) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    ButterflySpectatorGeometry.Width rows s.bits (2^ell) p (run s rows ell p rho visit n f) := by
  induction n with
  | zero => exact hw
  | succ n ih =>
    unfold run
    split_ifs with hi
    · exact ButterflySpectatorGeometry.width_apply _ _ _ _ _ _ _ ih
    · exact ih

def endpoint (n : ℕ) (f : Array s rows ell) :=
  CompactSpectatorLeafAxis.bank (initial s rows ell p rho.val (left+n) (arity^k))
    (CompactSpectatorLeafAxis.word (run s rows ell p rho visit n f))
def loop := CountedLoopHeaderClean.program CompactSpectatorLeafAxis.program 10

def bank (n : ℕ) (f : Array s rows ell) := CountedLoopHeaderClean.bank (endpoint s rows ell p rho visit n f)
def loopCost (_visit : Visit s.active left k) := CountedLoopHeaderClean.cost (arity^k) (RecursiveChildQuotientsConstant.bits (arity^k))
  (fun i => CompactSpectatorLeafAxis.cost s rows ell p rho.val (left+i) (arity^k))

theorem loops (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime loop (fun v => v=bank s rows ell p rho visit 0 f)
      (fun v => v=bank s rows ell p rho visit (arity^k) f) (loopCost s rows ell p rho visit) := by
  apply CountedLoopHeaderClean.runs CompactSpectatorLeafAxis.program 10
    (RecursiveChildQuotientsConstant.bits (arity^k)) (arity^k)
    (fun i => endpoint s rows ell p rho visit i f)
    (fun i => CompactSpectatorLeafAxis.cost s rows ell p rho.val (left+i) (arity^k))
    (by constructor <;> rfl) (RecursiveChildQuotientsConstant.bits_value _)
  intro i hi
  have hh := CompactSpectatorLeafAxis.runs_visit s rows ell p hr rho visit ⟨i,hi⟩
    (run s rows ell p rho visit i f) (width_run s rows ell p rho visit i f hw)
  simpa only [endpoint,run,dite_eq_left hi,Nat.add_assoc] using hh

def fields : List (Fin 43) :=
  [0,1,2,3,4,5,6,7,8,9,10]
def cleanup := extend (extend (extend (BinaryDescriptorCleanupList.program (a:=2) (by decide : 0<43) fields) 1)
  ButterflySpectatorPorts.count) 2

def values (_visit : Visit s.active left k) (ordinal : ℕ) : Fin 43 → List Bool := fun i =>
  RecursiveChildQuotientsConstant.bits (match i.val with
    | 0 => s.bits | 1 => rows | 2 => ell | 3 => p | 4 => s.chunk | 5 => rho.val
    | 6 => s.H | 7 => s.B | 8 => s.active | 9 => ordinal | 10 => arity^k | _ => 0)
def output (f : Array s rows ell) :=
  CountedLoopHeaderClean.bank (CompactSpectatorLeafAxis.bank (fun _ => none)
    (CompactSpectatorLeafAxis.word (run s rows ell p rho visit (arity^k) f)))

def program := seq loop cleanup

def cost := loopCost s rows ell p rho visit+
  BinaryDescriptorCleanupList.cost fields (values s rows ell p rho visit (left+arity^k))+1

theorem finalizes (f : Array s rows ell) :
    HoareTime cleanup (fun v => v=bank s rows ell p rho visit (arity^k) f)
      (fun v => v=output s rows ell p rho visit f)
      (BinaryDescriptorCleanupList.cost fields (values s rows ell p rho visit (left+arity^k))) := by
  have hh := BinaryDescriptorCleanupList.cleanup_hoare (a:=2) (by decide : 0<43)
    fields (by decide) (values s rows ell p rho visit (left+arity^k))
    (ActiveRepairRankHeadersCommands.bank (initial s rows ell p rho.val (left+arity^k) (arity^k))) (by
      intro i hi
      simp [fields] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals constructor
      all_goals first | rfl | (rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl))
  have he : BinaryDescriptorCleanupList.cleared fields
      (ActiveRepairRankHeadersCommands.bank (initial s rows ell p rho.val (left+arity^k) (arity^k)))=
      ActiveRepairRankHeadersCommands.bank (a:=2) (fun _ => none) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hc := hh.consequence (fun _ h => h) (fun v hv => hv.trans he) le_rfl
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hc
    (CountedLoopReuseAlphabet.one (CompactSpectatorLeafAxis.word (run s rows ell p rho visit (arity^k) f)) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)) (SharedBank.empty 2 2)

private theorem finishFor {q : ℕ} (M : Program (44+ButterflySpectatorPorts.count+2) q 2)
    (f : Array s rows ell)
    (hm : HoareTime M (fun v => v=bank s rows ell p rho visit 0 f)
      (fun v => v=bank s rows ell p rho visit (arity^k) f) (loopCost s rows ell p rho visit)) :
    HoareTime (seq M cleanup) (fun v => v=bank s rows ell p rho visit 0 f)
      (fun v => v=output s rows ell p rho visit f) (cost s rows ell p rho visit) := by
  exact (hm.seq (finalizes s rows ell p rho visit f)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem runs (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime program (fun v => v=bank s rows ell p rho visit 0 f)
      (fun v => v=output s rows ell p rho visit f) (cost s rows ell p rho visit) :=
  finishFor s rows ell p rho visit loop f (loops s rows ell p rho visit hr f hw)

end
end IntegerMultBounds.Machine.CompactSpectatorLeafLoop

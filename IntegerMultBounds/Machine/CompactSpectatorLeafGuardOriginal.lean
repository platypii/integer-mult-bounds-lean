import IntegerMultBounds.Machine.CompactSpectatorLeafOriginal
import IntegerMultBounds.Machine.CompactSpectatorInverseLeafOriginal
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardHeaders

/-! Original immutable precision is baseline q. The full generated address
width physically reserves both passes in private metadata before arithmetic.
Every descriptor lifecycle and axis pass is paid, with no intermediate resizing. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafGuardOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorLeafOriginal
open ButterflyIndependentGuardHeaders (reservation)

inductive Direction | forward | inverse deriving DecidableEq

def result (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (f : Array s rows ell) : Array s rows ell := match dir with
  | .forward => CompactSpectatorLeafLoop.run s rows ell (reservation s.bits q) rho visit (arity^k) f
  | .inverse => CompactSpectatorInverseLeafLoop.run s rows ell (reservation s.bits q) rho visit (arity^k) f

def loopProgram : Direction → Σ n,Program localCount n 2
  | .forward => ⟨_,CompactSpectatorLeafLoop.program⟩
  | .inverse => ⟨_,CompactSpectatorInverseLeafLoop.program⟩
def loopCost (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) : ℕ := match dir with
  | .forward => CompactSpectatorLeafLoop.cost s rows ell (reservation s.bits q) rho visit
  | .inverse => CompactSpectatorInverseLeafLoop.cost s rows ell (reservation s.bits q) rho visit

def reserve := extend (extend (extend (extend
  (ButterflyAxisHeadersArithmetic.compile (a:=2) CompactSpectatorLeafGuardHeaders.schedule).2 1)
  ButterflySpectatorPorts.count) 2) 15

def phaseProgram (dir : Direction) := seq (seq (seq (copies inputs).2 setup) reserve) (extend (loopProgram dir).2 15)

def phaseCost (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ) :=
  copyCost inputs (values s rows ell q rho.val left (arity^k) slots right source target)+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactSpectatorLeafSetup.schedule
    (CompactSpectatorLeafSetup.raw s rows ell q rho.val left (arity^k) slots right source target)+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactSpectatorLeafGuardHeaders.schedule
    (CompactSpectatorLeafHeaders.initial s rows ell q rho.val left (arity^k))+
  loopCost dir s rows ell q rho visit+3

private theorem loop_runs (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f) :
    HoareTime (loopProgram dir).2
      (fun v => v=localBank (CompactSpectatorLeafHeaders.initial s rows ell (reservation s.bits q) rho.val left (arity^k))
        (CompactSpectatorLeafAxis.word f))
      (fun v => v=localBank (fun _ => none) (CompactSpectatorLeafAxis.word (result dir s rows ell q rho visit f)))
      (loopCost dir s rows ell q rho visit) := by
  cases dir
  · exact CompactSpectatorLeafLoop.runs s rows ell (reservation s.bits q) rho visit hr f hw
  · exact CompactSpectatorInverseLeafLoop.runs s rows ell (reservation s.bits q) rho visit hr f hw

private theorem assembled {u v z t : ℕ} (A : Program tapes u 2) (B : Program tapes v 2)
    (C : Program tapes z 2) (D : Program tapes t 2)
    (input one two three output : Tapes tapes 2) (ca cb cc cd : ℕ)
    (ha : HoareTime A (fun x => x=input) (fun x => x=one) ca)
    (hb : HoareTime B (fun x => x=one) (fun x => x=two) cb)
    (hc : HoareTime C (fun x => x=two) (fun x => x=three) cc)
    (hd : HoareTime D (fun x => x=three) (fun x => x=output) cd) :
    HoareTime (seq (seq (seq A B) C) D) (fun x => x=input) (fun x => x=output) (ca+cb+cc+cd+3) := by
  exact (((ha.seq hb).seq hc).seq hd).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem phase_runs (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f) :
    HoareTime (phaseProgram dir)
      (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word f)
        (values s rows ell q rho.val left (arity^k) slots right source target))
      (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word (result dir s rows ell q rho visit f))
        (values s rows ell q rho.val left (arity^k) slots right source target))
      (phaseCost dir s rows ell q rho visit slots right source target) := by
  let vs := values s rows ell q rho.val left (arity^k) slots right source target
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := copies_runs inputs (List.nodup_finRange _) (fun _ => none) (CompactSpectatorLeafAxis.word f) vs
    (fun _ _ => rfl)
  dsimp [vs] at h0
  rw [copied_inputs] at h0
  have h1 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactSpectatorLeafSetup.runs s rows ell q rho.val left (arity^k) slots right source target hG hA hK)
    (CountedLoopReuseAlphabet.one (CompactSpectatorLeafAxis.word f) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)) (SharedBank.empty 2 2)) (originals vs)
  have h2 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactSpectatorLeafGuardHeaders.runs s rows ell q rho.val left (arity^k))
    (CountedLoopReuseAlphabet.one (CompactSpectatorLeafAxis.word f) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)) (SharedBank.empty 2 2)) (originals vs)
  have h3 := hoare_extend_eq (loop_runs dir s rows ell q rho visit hr f hw) (originals vs)
  exact assembled _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3

def roundtrip (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (f : Array s rows ell) :=
  result .inverse s rows ell q rho visit (result .forward s rows ell q rho visit f)
def program := seq (phaseProgram .forward) (phaseProgram .inverse)
def cost (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ) :=
  phaseCost .forward s rows ell q rho visit slots right source target+
  phaseCost .inverse s rows ell q rho visit slots right source target+1

private theorem roundtripFor {u v : ℕ} (A : Program tapes u 2) (B : Program tapes v 2)
    (input middle output : Tapes tapes 2) (ca cb : ℕ)
    (ha : HoareTime A (fun x => x=input) (fun x => x=middle) ca)
    (hb : HoareTime B (fun x => x=middle) (fun x => x=output) cb) :
    HoareTime (seq A B) (fun x => x=input) (fun x => x=output) (ca+cb+1) := by
  exact (ha.seq hb).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f) :
    HoareTime program
      (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word f)
        (values s rows ell q rho.val left (arity^k) slots right source target))
      (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word (roundtrip s rows ell q rho visit f))
        (values s rows ell q rho.val left (arity^k) slots right source target))
      (cost s rows ell q rho visit slots right source target) := by
  have hf := phase_runs .forward s rows ell q rho visit slots right source target hG hA hr f hw
  have hi := phase_runs .inverse s rows ell q rho visit slots right source target hG hA hr
    (result .forward s rows ell q rho visit f)
    (CompactSpectatorLeafLoop.width_run s rows ell (reservation s.bits q) rho visit (arity^k) f hw)
  exact roundtripFor _ _ _ _ _ _ _ hf hi

end
end IntegerMultBounds.Machine.CompactSpectatorLeafGuardOriginal

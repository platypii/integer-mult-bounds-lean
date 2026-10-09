import IntegerMultBounds.Machine.CompactSpectatorLeafOriginal
import IntegerMultBounds.Machine.CompactSpectatorInverseLeafLoop

/-! The inverse leaf uses the identical paid original-header copies and geometry,
followed by the actual swapped-merge spectator loop and complete cleanup. -/
namespace IntegerMultBounds.Machine.CompactSpectatorInverseLeafOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorLeafOriginal

def program := seq (seq (copies inputs).2 setup) (extend CompactSpectatorInverseLeafLoop.program 15)

def cost (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (slots right source target : ℕ) :=
  copyCost inputs (values s rows ell p rho.val left (arity^k) slots right source target)+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactSpectatorLeafSetup.schedule
    (CompactSpectatorLeafSetup.raw s rows ell p rho.val left (arity^k) slots right source target)+
  CompactSpectatorInverseLeafLoop.cost s rows ell p rho visit+2

private theorem assembled {u v z : ℕ} (A : Program tapes u 2) (B : Program tapes v 2) (C : Program tapes z 2)
    (input middle next output : Tapes tapes 2) (ca cb cc : ℕ)
    (ha : HoareTime A (fun x => x=input) (fun x => x=middle) ca)
    (hb : HoareTime B (fun x => x=middle) (fun x => x=next) cb)
    (hc : HoareTime C (fun x => x=next) (fun x => x=output) cc) :
    HoareTime (seq (seq A B) C) (fun x => x=input) (fun x => x=output) (ca+cb+cc+2) := by
  exact ((ha.seq hb).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime program
      (fun v => v=bank (fun _ => none) (CompactSpectatorInverseLeafAxis.word f)
        (values s rows ell p rho.val left (arity^k) slots right source target))
      (fun v => v=(CompactSpectatorInverseLeafLoop.output s rows ell p rho visit f).append
        (originals (values s rows ell p rho.val left (arity^k) slots right source target)))
      (cost s rows ell p rho visit slots right source target) := by
  let vs := values s rows ell p rho.val left (arity^k) slots right source target
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := copies_runs inputs (List.nodup_finRange _) (fun _ => none) (CompactSpectatorInverseLeafAxis.word f) vs
    (fun _ _ => rfl)
  dsimp [vs] at h0
  rw [copied_inputs] at h0
  have h1 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactSpectatorLeafSetup.runs s rows ell p rho.val left (arity^k) slots right source target hG hA hK)
    (CountedLoopReuseAlphabet.one (CompactSpectatorInverseLeafAxis.word f) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)) (SharedBank.empty 2 2)) (originals vs)
  have h2 := hoare_extend_eq (CompactSpectatorInverseLeafLoop.runs s rows ell p rho visit hr f hw) (originals vs)
  have hz : CompactSpectatorInverseLeafLoop.bank s rows ell p rho visit 0 f=
      localBank (CompactSpectatorLeafHeaders.initial s rows ell p rho.val left (arity^k))
        (CompactSpectatorInverseLeafAxis.word f) := by rfl
  rw [hz] at h2
  exact assembled _ _ _ _ _ _ _ _ _ _ h0 h1 h2

end
end IntegerMultBounds.Machine.CompactSpectatorInverseLeafOriginal

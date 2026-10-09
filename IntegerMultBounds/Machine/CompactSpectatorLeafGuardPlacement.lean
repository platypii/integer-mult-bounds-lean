import IntegerMultBounds.Machine.CompactSpectatorLeafPlacement
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardOriginal
import IntegerMultBounds.Machine.CompactSpectatorLeafSemantics

/-! Both paid guarded leaf passes execute at original native65/global109.
Original13 descriptors, immutable baseline q/ell, native-core workspace and all
other caller tapes are retained; every appended private tape is physically blank. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafGuardPlacement
noncomputable section
open CompactSpectatorLeafOriginal
open CompactSpectatorLeafPlacement
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)
variable {w : ℕ}

private theorem payload_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (hp : Function.Injective ps) (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.payload (setTape v (ps j) f p) ps=setTape (SharedBank.payload v ps) j f p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=j
  all_goals simp [SharedBank.payload,setTape,Function.update,hi,hp.eq_iff]

private theorem strip_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.strip (setTape v (ps j) f p) ps=SharedBank.strip v ps := by
  have hn (i : Fin n) (hi : ¬∃ k,ps k=i) : i≠ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j,ps j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals simp only [setTape,Function.update_of_ne (hn i hi)]

private theorem payload_replaced (f g : ℤ → Fin 6) (vs : Fin 15 → ℕ) :
    setTape (payload f vs) (Fin.castAdd 15 (0 : Fin 1)) g 0=payload g vs := by
  unfold payload
  rw [SharedPlacementAlphabet.setTape_append_left]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def phaseProgram (dir : Direction) := Placement.placed (CompactSpectatorLeafGuardOriginal.phaseProgram dir)
  (CleanSubbank.placement ports (common (w:=w)) common_injective)
def program := Placement.placed CompactSpectatorLeafGuardOriginal.program
  (CleanSubbank.placement ports (common (w:=w)) common_injective)

private theorem liftFor {n : ℕ} (M : Program tapes n 2) (f g : ℤ → Fin 6) (vs : Fin 15 → ℕ) (c : ℕ)
    (hm : HoareTime M (fun v => v=bank (fun _ => none) f vs) (fun v => v=bank (fun _ => none) g vs) c)
    (caller : Tapes (callerCount w) 2) (hdata : SharedBank.payload caller common=payload f vs) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports common common_injective))
      (fun v => v=CleanSubbank.bank (s:=tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=tapes)
        (setTape caller (common (Fin.castAdd 15 (0 : Fin 1))) g 0)) c := by
  apply CleanSubbank.realizes M ports common ports_injective common_injective
    caller (setTape caller (common (Fin.castAdd 15 (0 : Fin 1))) g 0)
    (bank (fun _ => none) f vs) (bank (fun _ => none) g vs) _
    ?_ ?_ (bank_clean _ _) (bank_clean _ _) ?_ hm
  · rw [bank_payload]; exact hdata.symm
  · rw [bank_payload,payload_update _ _ common_injective,hdata,payload_replaced]
  · exact (strip_update _ _ _ _ _).symm

theorem phase_runs (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right sourceSlot targetSlot : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hdata : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left (arity^k) slots right sourceSlot targetSlot)) :
    HoareTime (phaseProgram (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=tapes)
        (setTape caller (common (Fin.castAdd 15 (0 : Fin 1)))
          (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)) 0))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho visit slots right sourceSlot targetSlot) :=
  liftFor _ _ _ _ _ (CompactSpectatorLeafGuardOriginal.phase_runs dir s rows ell q rho visit slots right
    sourceSlot targetSlot hG hA hr f hw) caller hdata

theorem runs (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right sourceSlot targetSlot : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hdata : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left (arity^k) slots right sourceSlot targetSlot)) :
    HoareTime (program (w:=w))
      (fun v => v=CleanSubbank.bank (s:=tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=tapes)
        (setTape caller (common (Fin.castAdd 15 (0 : Fin 1)))
          (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)) 0))
      (CompactSpectatorLeafGuardOriginal.cost s rows ell q rho visit slots right sourceSlot targetSlot) :=
  liftFor _ _ _ _ _ (CompactSpectatorLeafGuardOriginal.runs s rows ell q rho visit slots right
    sourceSlot targetSlot hG hA hr f hw) caller hdata


theorem correct (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right sourceSlot targetSlot : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hfields : ∀ i,(f i).1.length=q+4*s.bits+4 ∧ (f i).2.length=q+4*s.bits+4)
    (hu : ∀ i,‖ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f i‖≤1)
    (caller : Tapes (callerCount w) 2)
    (hdata : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left (arity^k) slots right sourceSlot targetSlot)) :
    HoareTime (program (w:=w))
      (fun v => v=CleanSubbank.bank (s:=tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=tapes)
        (setTape caller (common (Fin.castAdd 15 (0 : Fin 1)))
          (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)) 0) ∧
        ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q (2*arity^k)
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)=
          ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f)
      (CompactSpectatorLeafGuardOriginal.cost s rows ell q rho visit slots right sourceSlot targetSlot) := by
  have hw := CompactSpectatorLeafGuardHeaders.readiness s rows ell q f hfields
  have hh := runs s rows ell q rho visit slots right sourceSlot targetSlot hG hA hr f hw caller hdata
  have he := CompactSpectatorLeafSemantics.roundtrip_whole s rows ell q rho visit f hw hu
  exact hh.consequence (fun _ h => h) (fun _ h => ⟨h,he⟩) le_rfl

end
end IntegerMultBounds.Machine.CompactSpectatorLeafGuardPlacement

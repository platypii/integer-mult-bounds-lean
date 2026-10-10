import IntegerMultBounds.Machine.CompactSpectatorStoppedLeafCaller
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! The stopped leaf reads the live canonical controller exponent at global1.
Exponent0 executes the actual scalar phase; a positive exponent physically
expands/restores the parent slot count around the actual guarded phase. -/
namespace IntegerMultBounds.Machine.CompactSpectatorStoppedLeafDispatch
noncomputable section
open CompactSpectatorStoppedLeafCaller
open CompactSpectatorLeafOriginal
open CompactSpectatorLeafPlacement
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open RecursiveChildQuotientsConstant (bits)
variable {w : ℕ}

def exponentSlot : Fin (total (w:=w)) := ⟨1,by unfold total outer callerCount; omega⟩
def test (sy : Fin (total (w:=w)) → Fin 6) := decide (sy exponentSlot=blank)
def program (dir : CompactSpectatorLeafGuardOriginal.Direction) :=
  branch (test (w:=w)) (scalarPhaseProgram (w:=w) dir) (positivePhaseProgram (w:=w) dir)

private theorem encoded_blank_iff (bs : List Bool) :
    RadixZeroFill.encodedBinary (q:=2) bs 1=blank ↔ bs=[] := by
  rw [← BinaryDescriptorStackRoundtrip.descriptor_encoded]
  cases bs with
  | nil => simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty]
  | cons b bs => cases b <;> simp [BinaryDescriptorStack.descriptor,putWord,bitSymbol,blank,Fin.ext_iff]

theorem decision (caller : Tapes (callerCount w) 2) (e : ℕ)
    (ht : caller.tape ⟨1,by unfold callerCount; omega⟩=RadixZeroFill.encodedBinary (bits e))
    (hh : caller.head ⟨1,by unfold callerCount; omega⟩=1) :
    test (CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller)).reads=decide (e=0) := by
  have hn : bits e=[] ↔ e=0 := by
    constructor
    · intro h; have hv := RecursiveChildQuotientsConstant.bits_value e; rw [h] at hv; exact hv.symm
    · intro h; apply BinaryCanonicalData.zero_nil _ (RecursiveChildQuotientsConstant.bits_canonical e)
      rw [RecursiveChildQuotientsConstant.bits_value,h]
  unfold test Tapes.reads exponentSlot
  change decide (caller.tape ⟨1,_⟩ (caller.head ⟨1,_⟩)=blank)=_
  rw [ht,hh]
  simp only [encoded_blank_iff,hn]

private theorem branch_left {t q r b : ℕ} (select : (Fin t → Fin 6) → Bool)
    (M : Program t q 2) (N : Program t r 2) (v : Tapes t 2) (post : TapePred t 2)
    (hs : select v.reads=true) (hm : HoareTime M (fun x => x=v) post b) :
    HoareTime (branch select M N) (fun x => x=v) post (b+1) := by
  have hl : HoareTime M (fun x => x=v ∧ select x.reads=true) post b :=
    hm.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
  have hr : HoareTime N (fun x => x=v ∧ select x.reads=false) post 0 := by
    rintro x ⟨rfl,h⟩; rw [hs] at h; contradiction
  simpa using branch_hoare select hl hr

private theorem branch_right {t q r b : ℕ} (select : (Fin t → Fin 6) → Bool)
    (M : Program t q 2) (N : Program t r 2) (v : Tapes t 2) (post : TapePred t 2)
    (hs : select v.reads=false) (hm : HoareTime N (fun x => x=v) post b) :
    HoareTime (branch select M N) (fun x => x=v) post (b+1) := by
  have hl : HoareTime M (fun x => x=v ∧ select x.reads=true) post 0 := by
    rintro x ⟨rfl,h⟩; rw [hs] at h; contradiction
  have hr : HoareTime N (fun x => x=v ∧ select x.reads=false) post b :=
    hm.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
  simpa using branch_hoare select hl hr

theorem positive_runs (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair))
    (ht : caller.tape ⟨1,by unfold callerCount; omega⟩=RadixZeroFill.encodedBinary (bits (k+1)))
    (hh : caller.head ⟨1,by unfold callerCount; omega⟩=1) :
    HoareTime (program (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)))))
      (positivePhaseCost dir s rows ell q rho visit hactive pair+1) := by
  apply branch_right _ _ _ _ _ ?_
    (positive_phase_runs dir s rows ell q rho visit hactive pair hG hA hr f hw caller hd)
  rw [decision caller (k+1) ht hh]
  simp

theorem scalar_runs (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 1) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (scalarValues s rows ell q rho slot pair left))
    (ht : caller.tape ⟨1,by unfold callerCount; omega⟩=RadixZeroFill.encodedBinary (bits 0))
    (hh : caller.head ⟨1,by unfold callerCount; omega⟩=1) :
    HoareTime (program (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho (Visit.child visit slot) f)))))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho (Visit.child visit slot) arity
        (s.active-(left+slot.val+1)) pair.source.val pair.target.val+1) := by
  apply branch_left _ _ _ _ _ ?_
    (scalar_actual_phase_runs dir s rows ell q rho visit slot pair hG hA hr f hw caller hd)
  rw [decision caller 0 ht hh]
  rfl

end
end IntegerMultBounds.Machine.CompactSpectatorStoppedLeafDispatch

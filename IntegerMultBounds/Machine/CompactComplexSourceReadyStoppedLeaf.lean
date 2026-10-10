import IntegerMultBounds.Machine.CompactComplexSourceReadyLeafDenominator
import IntegerMultBounds.Machine.CompactComplexSourceReadyLeafSemantics

/-! Actual stopped source-ready execution through restored raw geometry and
physical leaf-target/live installation. One fixed leaf-plus-ten suffix suffices;
rows, vacant roles and saved parent/ancestor frames remain untouched. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeaf
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

abbrev publicTapes (s c : ℕ) := CompactComplexNonleafRoleChildBank.tapes s c
abbrev tapes (s c : ℕ) := CompactComplexSourceReadyLeafDenominator.tapes s c

def ready (v : Tapes (publicTapes s c) 2) :=
  (CompactComplexSourceReadyLeafPhase.ready v).append (SharedBank.empty 10 2)
def program (dir : Direction) := seq
  (extend (CompactComplexSourceReadyLeaf.program (s:=10+s) (c:=c) dir) 10)
  (CompactComplexSourceReadyLeafDenominator.program (s:=s) (c:=c))
def output (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (targetN : ℕ) :=
  CompactComplexSourceReadyLeafDenominator.output
    (ready (setTape v (CompactComplexSourceReadyLeafPhase.source (s:=10+s)) f 0)) targetN

private theorem source_current : CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠
    CompactComplexNonleafRoleChildBank.current (s:=s) := by
  intro h
  have hv := congrArg Fin.val h
  simp [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleChildBank.current,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.storageSlot] at hv
private theorem source_target : CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠
    CompactComplexNonleafRoleChildBank.target (s:=s) := by
  intro h
  have hv := congrArg Fin.val h
  simp [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleChildBank.target,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.storageSlot] at hv
private theorem source_volume : CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠
    CompactComplexNonleafRoleChildBank.numeric (s:=s) 7 := by
  intro h
  have hv := congrArg Fin.val h
  simp [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexNonleafRoleChildBank.numeric,
    CompactComplexNonleafRoleEntry.numeric,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot] at hv

/-- Actual leaf execution restores its raw row descriptor, constructs its own
true target from the retained volume and commits it to live7, clearing target8. -/
theorem runs (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k) (slots right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) slots right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho visit f)) (CompactComplexDenominatorPolicy.leafTarget n k))
      (CompactComplexSourceReadyLeaf.cost dir sh rows ell p rho visit slots right src dst+
        CompactNativeDenominatorTarget.leafCost n (arity^k)+2*(bits n).length+
        4*(bits (CompactComplexDenominatorPolicy.leafTarget n k)).length+17) := by
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir
    (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f)
  let after := ready (setTape v (CompactComplexSourceReadyLeafPhase.source (s:=10+s)) g 0)
  have h0 := hoare_extend_eq (CompactComplexSourceReadyLeaf.runs dir sh rows ell p rho visit slots right src dst
    v f hG hA hr hp hw hraw hsource) (SharedBank.empty 10 2)
  have hn : after.head CompactComplexSourceReadyLeafDenominator.current=1 ∧
      after.tape CompactComplexSourceReadyLeafDenominator.current=RadixZeroFill.encodedBinary (bits n) := by
    simpa only [after,ready,CompactComplexSourceReadyLeafPhase.ready,
      CompactComplexSourceReadyLeafDenominator.current,Tapes.append,Fin.addCases_left,setTape,
      Function.update_of_ne (source_current (s:=s) (c:=c)).symm] using hlive
  have ht : after.head CompactComplexSourceReadyLeafDenominator.target=0 ∧
      after.tape CompactComplexSourceReadyLeafDenominator.target=(fun _ => blank) := by
    simpa only [after,ready,CompactComplexSourceReadyLeafPhase.ready,
      CompactComplexSourceReadyLeafDenominator.target,Tapes.append,Fin.addCases_left,setTape,
      Function.update_of_ne (source_target (s:=s) (c:=c)).symm] using htarget
  have hwk : after.head CompactComplexSourceReadyLeafDenominator.work=0 ∧
      after.tape CompactComplexSourceReadyLeafDenominator.work=(fun _ => blank) := by
    simp [after,ready,CompactComplexSourceReadyLeafDenominator.work,Tapes.append,SharedBank.empty]
  have hvol : v.head (CompactComplexNonleafRoleChildBank.numeric 7)=1 ∧
      v.tape (CompactComplexNonleafRoleChildBank.numeric 7)=RadixZeroFill.encodedBinary (bits (arity^k)) := by
    have h := congrArg (fun z : Tapes 43 2 => (z.head 7,z.tape 7)) hraw
    simp only [Placement.active,headerPlacement,InjectivePlacement.active_slot,base] at h
    exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
  have hv : after.head CompactComplexSourceReadyLeafDenominator.volume=1 ∧
      after.tape CompactComplexSourceReadyLeafDenominator.volume=RadixZeroFill.encodedBinary (bits (arity^k)) := by
    simpa only [after,ready,CompactComplexSourceReadyLeafPhase.ready,
      CompactComplexSourceReadyLeafDenominator.volume,Tapes.append,Fin.addCases_left,setTape,
      Function.update_of_ne (source_volume (s:=s) (c:=c)).symm] using hvol
  have h1 := CompactComplexSourceReadyLeafDenominator.runs after n (arity^k) hn hv ht hwk
  exact (h0.seq h1).consequence (fun _ hz => hz) (fun _ hz => hz) (by unfold CompactComplexDenominatorPolicy.leafTarget;omega)

/-- The complete stopped endpoint is one literal source-ready public bank;
every borrowed private tape is blank and parked ancestor payloads are retained. -/
theorem output_eq_ready (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ) :
    output v f n=ready
      (setTape (setTape (setTape v (CompactComplexSourceReadyLeafPhase.source (s:=10+s)) f 0)
        CompactComplexNonleafRoleChildBank.current (RadixZeroFill.encodedBinary (bits n)) 1)
        CompactComplexNonleafRoleChildBank.target (fun _ => blank) 0) := by
  unfold output CompactComplexSourceReadyLeafDenominator.output ready CompactComplexSourceReadyLeafPhase.ready
    CompactComplexSourceReadyLeafDenominator.current CompactComplexSourceReadyLeafDenominator.target
  repeat rw [SharedPlacementAlphabet.setTape_append_left]

theorem output_frame (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ)
    (i : Fin (publicTapes s c))
    (hs : i≠CompactComplexSourceReadyLeafPhase.source (s:=10+s))
    (hc : i≠CompactComplexNonleafRoleChildBank.current)
    (ht : i≠CompactComplexNonleafRoleChildBank.target) :
    (output v f n).head (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyLeafPhase.privateTapes i))=v.head i ∧
    (output v f n).tape (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyLeafPhase.privateTapes i))=v.tape i := by
  rw [output_eq_ready]
  simp only [ready,CompactComplexSourceReadyLeafPhase.ready,Tapes.append,Fin.addCases_left,setTape,
    Function.update_of_ne hs,Function.update_of_ne hc,Function.update_of_ne ht,and_self]

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeaf

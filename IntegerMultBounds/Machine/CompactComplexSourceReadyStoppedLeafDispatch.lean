import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! One fixed stopped-node body reads the actual exponent word before choosing
scalar execution or physical per-child count expansion and restoration. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatch
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def exponent : Fin (CompactComplexSourceReadyLeafDenominator.tapes s c) :=
  Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyLeafPhase.privateTapes
    (CompactComplexNonleafRoleChildBank.control 1))
def test (sy : Fin (CompactComplexSourceReadyLeafDenominator.tapes s c) → Fin 6) :=
  decide (sy exponent=blank)
def program (dir : Direction) := branch (test (s:=s) (c:=c))
  (CompactComplexSourceReadyStoppedLeaf.program (s:=s) (c:=c) dir)
  (CompactComplexSourceReadyStoppedLeafCount.program (s:=s) (c:=c) dir)

private theorem encoded_blank_iff (bs : List Bool) :
    RadixZeroFill.encodedBinary (q:=2) bs 1=blank ↔ bs=[] := by
  rw [←BinaryDescriptorStackRoundtrip.descriptor_encoded]
  cases bs with
  | nil => simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty]
  | cons b bs => cases b <;> simp [BinaryDescriptorStack.descriptor,putWord,bitSymbol,blank,Fin.ext_iff]

theorem decision (v : Tapes (publicTapes s c) 2) (e : ℕ)
    (ht : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits e))
    (hh : v.head (CompactComplexNonleafRoleChildBank.control 1)=1) :
    test (ready v).reads=decide (e=0) := by
  have hn : bits e=[] ↔ e=0 := by
    constructor
    · intro h;have hv := RecursiveChildQuotientsConstant.bits_value e;rw [h] at hv;exact hv.symm
    · intro h;apply BinaryCanonicalData.zero_nil _ (RecursiveChildQuotientsConstant.bits_canonical e)
      rw [RecursiveChildQuotientsConstant.bits_value,h]
  unfold test Tapes.reads exponent
  simp only [ready,CompactComplexSourceReadyLeafPhase.ready,Tapes.append,Fin.addCases_left,ht,hh,encoded_blank_iff,hn]

private theorem branch_left {t q r b : ℕ} (select : (Fin t → Fin 6) → Bool)
    (M : Program t q 2) (N : Program t r 2) (v : Tapes t 2) (post : TapePred t 2)
    (hs : select v.reads=true) (hm : HoareTime M (fun x => x=v) post b) :
    HoareTime (branch select M N) (fun x => x=v) post (b+1) := by
  have hl : HoareTime M (fun x => x=v ∧ select x.reads=true) post b :=
    hm.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
  have hr : HoareTime N (fun x => x=v ∧ select x.reads=false) post 0 := by
    rintro x ⟨rfl,h⟩;rw [hs] at h;contradiction
  simpa using branch_hoare select hl hr
private theorem branch_right {t q r b : ℕ} (select : (Fin t → Fin 6) → Bool)
    (M : Program t q 2) (N : Program t r 2) (v : Tapes t 2) (post : TapePred t 2)
    (hs : select v.reads=false) (hm : HoareTime N (fun x => x=v) post b) :
    HoareTime (branch select M N) (fun x => x=v) post (b+1) := by
  have hl : HoareTime M (fun x => x=v ∧ select x.reads=true) post 0 := by
    rintro x ⟨rfl,h⟩;rw [hs] at h;contradiction
  have hr : HoareTime N (fun x => x=v ∧ select x.reads=false) post b :=
    hm.consequence (fun _ h => h.1) (fun _ h => h) le_rfl
  simpa using branch_hoare select hl hr

theorem positive_runs (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left (k+1)) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=ready (returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1))))
      (CompactComplexSourceReadyStoppedLeafCount.cost dir sh rows ell p rho visit right src dst n+1) := by
  apply branch_right _ _ _ _ _ ?_
    (CompactComplexSourceReadyStoppedLeafCount.runs dir sh rows ell p rho visit right src dst n
      v f hG hA hr hp hw hraw hsource hlive htarget)
  rw [decision v (k+1) hexponent hexponentHead]
  simp

theorem scalar_runs (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left : ℕ} (visit : Visit sh.active left 0) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho visit f)) (CompactComplexDenominatorPolicy.leafTarget n 0))
      (CompactComplexSourceReadyStoppedLeafBudget.fullCost dir sh rows ell p rho visit arity right src dst n+1) := by
  apply branch_left _ _ _ _ _ ?_
    (CompactComplexSourceReadyStoppedLeaf.runs dir sh rows ell p rho visit arity right src dst n
      v f hG hA hr hp hw hraw hsource hlive htarget)
  rw [decision v 0 hexponent hexponentHead]
  rfl

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatch

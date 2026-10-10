import IntegerMultBounds.Machine.NativeEndpointCharacterHeaders
import IntegerMultBounds.Machine.AllAxisPolynomialPlacement

/-! Literal aggregate sign-character traversal from the caller's original
numeric descriptors, with complete private-workspace cleanup. The fixed
weight list is compiled; polynomial multiplicity and address width are read
from retained runtime headers. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterLifecycle
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape sharedPlacement)
open NativeEndpointCharacterHeaders (words initial ready tail)
variable {s : Shape} {t : ℕ}

private theorem right_frame {n q k : ℕ} {M : Program n q 2} {x y : Tapes n 2}
    (h : HoareTime M (fun z => z=x) (fun z => z=y) k) (caller : Tapes t 2) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun z => z=caller.append x) (fun z => z=caller.append y) k := by
  have he (z : Tapes n 2) : Placement.combine finAddFlip z caller=caller.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x caller)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun z hz => hz.trans (he x).symm) _ le_rfl
  rintro z ⟨u,hu,rfl⟩
  subst u
  simpa only [Placement.replace,Placement.extra_combine] using he y

def metadataSetup (order : Order) := Placement.placed
  (AllAxisPhaseStageMetadata.setup (a:=2) (extra:=24) order)
  (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def metadataCleanup := Placement.placed
  (AllAxisPhaseStageMetadata.cleanup (a:=2) (extra:=24))
  (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def call (src : Fin t) (m : ℕ) (ws : List (ZMod 4)) :=
  Placement.placed (extend (AllAxisPolynomialNative.program m ws) 1)
    (sharedPlacement src (56 : Fin 67))
def program (focus : Fin 14 → Fin t) (src : Fin t) (order : Order)
    (m : ℕ) (ws : List (ZMod 4)) :=
  seq (NativeEndpointCharacterHeaders.copy focus)
    (seq (metadataSetup order) (seq (call src m ws)
      (seq metadataCleanup (NativeEndpointCharacterHeaders.erase (t:=t)))))

theorem ready_eq (order : Order) (v : Stage s) (rows ell : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    ready order v rows ell=setTape (AllAxisPolynomialPlacement.input order v rows ell xs)
      56 (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=43) (n:=24) with
    | left i =>
      have hn : Fin.castAdd 24 i≠(56 : Fin 67) := by
        intro h; have hv := congrArg Fin.val h
        change i.val=56 at hv
        have hi := i.isLt; omega
      have he : Fin.castAdd 24 i=Fin.castAdd 1 (Fin.castAdd 6 (Fin.castAdd 17 i)) := Fin.ext rfl
      simp only [Function.update_of_ne hn,Fin.addCases_left]
      rw [he]
      simp only [AllAxisPolynomialPlacement.input,AllAxisPolynomialStreamInit.input,
        AllAxisFullStreamInit.input,AllAxisPhaseStreamInit.input,AllAxisAddressHeaders.initial,
        AllAxisPhaseHeadersData.initial,Tapes.append,Fin.addCases_left]
    | right i => fin_cases i <;> rfl
  · funext i
    induction i using Fin.addCases (m:=43) (n:=24) with
    | left i =>
      have hn : Fin.castAdd 24 i≠(56 : Fin 67) := by
        intro h; have hv := congrArg Fin.val h
        change i.val=56 at hv
        have hi := i.isLt; omega
      have he : Fin.castAdd 24 i=Fin.castAdd 1 (Fin.castAdd 6 (Fin.castAdd 17 i)) := Fin.ext rfl
      simp only [Function.update_of_ne hn,Fin.addCases_left]
      rw [he]
      simp only [AllAxisPolynomialPlacement.input,AllAxisPolynomialStreamInit.input,
        AllAxisFullStreamInit.input,AllAxisPhaseStreamInit.input,AllAxisAddressHeaders.initial,
        AllAxisPhaseHeadersData.initial,Tapes.append,Fin.addCases_left]
    | right i => fin_cases i <;> rfl

def resultCaller (caller : Tapes t 2) (src : Fin t) (v : Stage s) (m : ℕ)
    (ws : List (ZMod 4)) {rows ell : ℕ}
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient) :=
  setTape caller src (putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized
    (AllAxisPolynomialLiteralEndpoint.result v m ws xs))) 0

theorem call_runs (src : Fin t) (caller : Tapes t 2) (order : Order)
    (v : Stage s) (rows : ℕ) (hr : 0<rows) (m : ℕ) (ws : List (ZMod 4))
    (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hs : caller.tape src=putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs))
    (hp : caller.head src=0) :
    HoareTime (call src m ws) (fun z => z=caller.append (ready order v rows ell))
      (fun z => z=(resultCaller caller src v m ws xs).append (ready order v rows ell))
      (AllAxisPolynomialNative.cost order v rows m ell w) := by
  have h0 := hoare_extend_eq
    (AllAxisPolynomialNative.runs order v rows hr m ws hm hslots hl hspan ell w xs hw)
    (SharedBank.empty 1 2)
  have h1 := SharedPlacementAlphabet.shared_hoare h0 caller src (56 : Fin 67)
    (fun _ => blank) 0 hs hp
  change HoareTime (call src m ws)
    (fun z => z=caller.append (setTape (AllAxisPolynomialPlacement.input order v rows ell xs) 56 (fun _ => blank) 0))
    (fun z => z=(resultCaller caller src v m ws xs).append
      (setTape (AllAxisPolynomialPlacement.output order v rows m ws ell xs) 56 (fun _ => blank) 0)) _ at h1
  rwa [AllAxisPolynomialPlacement.cleared_output,←ready_eq] at h1

def cost (order : Order) (v : Stage s) (rows m ell w : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 14) (words v rows ell)+1+
    (ActivePrefixStageHeadersRun.cost order v rows+1+
      (AllAxisPolynomialNative.cost order v rows m ell w+1+
        (AllAxisPhaseStageMetadata.cleanupCost order v rows+1+
          FixedHeaderBankCopy.cleanupCost (t:=t) (words v rows ell))))

theorem runs (focus : Fin 14 → Fin t) (src : Fin t) (caller : Tapes t 2)
    (order : Order) (v : Stage s) (rows : ℕ) (hG : 1≤s.guard)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) (hr : 0<rows)
    (m : ℕ) (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots)
    (hl : m=ws.length)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (ell w : ℕ) (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hheaders : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary (words v rows ell i))
    (hheads : ∀ i,caller.head (focus i)=1)
    (hs : caller.tape src=putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs))
    (hp : caller.head src=0) :
    HoareTime (program focus src order m ws)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(resultCaller caller src v m ws xs).append (FixedHeaderBankCopy.empty 67))
      (cost (t:=t) order v rows m ell w) := by
  have hcopy := NativeEndpointCharacterHeaders.copy_runs focus caller v rows ell hheaders hheads
  have hsetup := right_frame (AllAxisPhaseStageMetadata.setup_runs order v rows (tail ell) hG ho) caller
  have hcall := call_runs src caller order v rows hr m ws hm hslots hl hspan ell w xs hw hs hp
  have hclean := right_frame (AllAxisPhaseStageMetadata.cleanup_runs order v rows (tail ell))
    (resultCaller caller src v m ws xs)
  have herase := NativeEndpointCharacterHeaders.erase_runs (resultCaller caller src v m ws xs) v rows ell
  exact hcopy.seq (hsetup.seq (hcall.seq (hclean.seq herase)))

end
end IntegerMultBounds.Machine.NativeEndpointCharacterLifecycle

import IntegerMultBounds.Machine.CompactComplexExactReturnFamily
import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHeaders
import IntegerMultBounds.Machine.CompactComplexControllerAlignedCommit
import IntegerMultBounds.Machine.CompactComplexDenominatorPolicy

/-! Exact completed-network returns contract every genuine permanent role,
install the true target denominator and erase generated length metadata.
Coarser-grid correctness is a semantic obligation of the completed nonleaf;
retained signed-field capacity alone does not imply exact contraction. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerExactReturn
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSpectatorTargetBank (roleSlot oldSlot numericSlot)
open CompactComplexSpectatorVolumeHeaders
open ActiveRepairRankHeadersCommands (State)
open CompactGadgetReservationShape (Shape)
open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (volume)
open NativeSignedGapReturn (word)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

private theorem different : (⟨7,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  norm_num at hv

private def family := CompactComplexExactReturnFamily.compile
  (roleSlot (s:=10+s) (c:=c)) (oldSlot ⟨7,by omega⟩) (oldSlot ⟨8,by omega⟩) (numericSlot 27)
  (CompactComplexSpectatorTargetBank.ports_injective ⟨7,by omega⟩ ⟨8,by omega⟩ different 27)
  (List.finRange c)

def returned (ws : Fin c → List Word) (current target : ℕ) (payload : Tapes (1+c) 2) :=
  CompactComplexSpectatorRoleSchedule.execute
    (fun j => word ((ws j).map (NativeSignedGapScan.result (current-target)))) (List.finRange c) payload

def committed (storage : Tapes (10+s) 2) (targetN : ℕ) :=
  setTape (setTape storage (⟨7,by omega⟩ : Fin (10+s)) (RadixZeroFill.encodedBinary (bits targetN)) 1)
    ⟨8,by omega⟩ (fun _ => blank) 0

private theorem output_bank (control : Tapes 43 2) (queue : Tapes 1 2) (scalar stage : State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (targetN : ℕ) :
    CompactComplexControllerAlignedCommit.output (bank control queue scalar stage tail storage payload) targetN=
      bank control queue scalar stage tail (committed storage targetN) payload := by
  unfold CompactComplexControllerAlignedCommit.output CompactComplexControllerAlignedCommit.current
    CompactComplexControllerAlignedCommit.target CompactComplexSpectatorTargetBank.oldSlot
    bank CompactComplexNativeRoleBridge.bank CompactComplexControllerNativeFrame.storageSlot
    CompactComplexControllerNativeFrame.bank committed
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_right,
    SharedPlacementAlphabet.setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

private def compose {t : ℕ} (p q : Σ r,Program t r 2) : Σ r,Program t r 2 := ⟨_,seq p.2 q.2⟩
private theorem compose_runs {t : ℕ} (p q : Σ r,Program t r 2)
    {pre mid post : TapePred t 2} {A B : ℕ} (h0 : HoareTime p.2 pre mid A)
    (h1 : HoareTime q.2 mid post B) : HoareTime (compose p q).2 pre post (A+1+B) := h0.seq h1

def program (headerCount : ℕ) (merge : Bool) :
    Σ q,Program (permanentTapes (10+s) c+10) q 2 :=
  compose (compose (compose
    ⟨_,extend (headerProgram (s:=10+s) (c:=c) (CompactNativeRoleHeaders.schedule headerCount merge)) 10⟩
    (family (s:=s) (c:=c)))
    ⟨_,extend (headerProgram (s:=10+s) (c:=c) CompactNativeRoleHeaders.cleanup) 10⟩)
    ⟨_,extend (CompactComplexControllerAlignedCommit.program (s:=s) (c:=c)) 10⟩

private theorem family_runs (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+c) 2) (ws : Fin c → List Word)
    (current target V : ℕ) (hle : target≤current) (ls : List Bool)
    (hd : ∀ j w,w∈ws j → current-target≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hlen : Counter.value ls=V)
    (hcanonical : GrowingCounterData.Canonical ls)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target))
    (hl : (bank control queue scalar stage tail storage payload).head (numericSlot 27)=1 ∧
      (bank control queue scalar stage tail storage payload).tape (numericSlot 27)=RadixZeroFill.encodedBinary ls)
    (hs : ∀ j,(bank control queue scalar stage tail storage payload).head (roleSlot j)=0 ∧
      (bank control queue scalar stage tail storage payload).tape (roleSlot j)=word (ws j)) :
    HoareTime (family (s:=s) (c:=c)).2
      (fun z => z=CompactComplexExactReturnFamily.ready (bank control queue scalar stage tail storage payload))
      (fun z => z=CompactComplexExactReturnFamily.ready
        (bank control queue scalar stage tail storage (returned ws current target payload)))
      (c*(129*V+8*current+360)) := by
  have hcur := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload ⟨7,by omega⟩
  have htar := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload ⟨8,by omega⟩
  have h := CompactComplexExactReturnFamily.compile_runs roleSlot
    CompactComplexSpectatorTargetBank.role_injective _ _ _
    (CompactComplexSpectatorTargetBank.ports_injective ⟨7,by omega⟩ ⟨8,by omega⟩ different 27)
    ws (List.finRange c) (List.nodup_finRange _) (bank control queue scalar stage tail storage payload)
    current target V hle ls hd hn hv hlen hcanonical
    ⟨hcur.1.trans hc.1,hcur.2.trans hc.2⟩ ⟨htar.1.trans ht.1,htar.2.trans ht.2⟩ hl
    (fun j _ => hs j)
  rw [CompactComplexSpectatorTargetBank.bank_execute] at h
  simpa only [family,returned,List.length_finRange] using h

private theorem commit_runs (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : State) (tail : Tapes 22 2) (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (current target : ℕ)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target)) :
    HoareTime (extend (CompactComplexControllerAlignedCommit.program (s:=s) (c:=c)) 10)
      (fun z => z=CompactComplexExactReturnFamily.ready (bank control queue scalar stage tail storage payload))
      (fun z => z=CompactComplexExactReturnFamily.ready (bank control queue scalar stage tail (committed storage target) payload))
      (2*(bits current).length+4*(bits target).length+15) := by
  have hcur := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload ⟨7,by omega⟩
  have htar := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload ⟨8,by omega⟩
  have h := CompactComplexControllerAlignedCommit.runs (bank control queue scalar stage tail storage payload)
    current target (hcur.2.trans hc.2) (hcur.1.trans hc.1) (htar.2.trans ht.2) (htar.1.trans ht.1)
  rw [output_bank] at h
  exact hoare_extend_eq h (SharedBank.empty 10 2)


/-- Clean execution on a permanent caller bank and ten restored private tapes. -/
def Realizes {t : ℕ} (P : Σ q,Program (t+10) q 2) (v0 v1 : Tapes t 2) (cost : ℕ) :=
  HoareTime P.2 (fun z => z=CompactComplexExactReturnFamily.ready v0)
    (fun z => z=CompactComplexExactReturnFamily.ready v1) cost

attribute [local irreducible] CompactComplexExactReturnFamily.compile seq

/-- Original retained geometry generates the real stream-volume header. Every
role is contracted, generated metadata is erased, then the true denominator
is installed; the original scalar suffix and all controller stacks remain. -/
theorem raw_runs (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current target : ℕ) (hle : target≤current)
    (hcapacity : current-target≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j))) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage target) (returned ws current target payload))
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
        c*(129*streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+
        (2*(bits current).length+4*(bits target).length+15)+3) := by
  dsimp only
  let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
  let prep := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
  let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
  let V := streamVolume sh headerCount rows ell metadataP merge
  have hrr : 0<roleRows headerCount rows merge := by cases merge <;> assumption
  have hv : ∀ j,volume (ws j)=V := by
    intro j
    rw [CompactComplexStoppedGridHandoff.words_volume sh _ ell _ (f j) (hw j)]
    exact (volume_semantic sh headerCount rows ell metadataP merge hmetadata).symm
  have hn : ∀ j,ws j≠[] := fun j =>
    CompactComplexStoppedGridHandoff.words_nonempty sh _ ell _ hrr (f j) (hw j)
  have hd : ∀ j w,w∈ws j → current-target≤w.length := by
    intro j w hmem
    rw [CompactComplexStoppedGridHandoff.words_width sh _ ell _ (f j) (hw j) w hmem]
    exact hcapacity
  have hp := hoare_extend_eq (prepare_runs sh headerCount rows ell metadataP rho left count slots right src dst
    merge hcount hr hgroup hG hA hK control queue scalar tail storage payload) (SharedBank.empty 10 2)
  have hl := prepared_length sh headerCount rows ell metadataP rho left count slots right src dst
    merge control queue scalar tail storage payload
  have hsource : ∀ j,(bank control queue scalar prep tail storage payload).head (roleSlot j)=0 ∧
      (bank control queue scalar prep tail storage payload).tape (roleSlot j)=word (ws j) := by
    intro j
    have he := CompactComplexSpectatorTargetBank.role_bank control queue scalar prep tail storage payload j
    exact ⟨he.1.trans (hs j).1,he.2.trans (hs j).2⟩
  have hf := family_runs control queue scalar prep tail storage payload ws current target V hle
    (bits V) hd hn hv (RecursiveChildQuotientsConstant.bits_value V)
    (RecursiveChildQuotientsConstant.bits_canonical V) hc ht hl hsource
  have hclean := hoare_extend_eq (cleanup_runs sh headerCount rows ell metadataP rho left count slots right src dst
    merge control queue scalar tail storage (returned ws current target payload)) (SharedBank.empty 10 2)
  have hcommit := commit_runs control queue scalar old tail storage (returned ws current target payload) current target hc ht
  let pp : Σ q,Program (permanentTapes (10+s) c+10) q 2 :=
    ⟨_,extend (headerProgram (s:=10+s) (c:=c) (CompactNativeRoleHeaders.schedule headerCount merge)) 10⟩
  let cp : Σ q,Program (permanentTapes (10+s) c+10) q 2 :=
    ⟨_,extend (headerProgram (s:=10+s) (c:=c) CompactNativeRoleHeaders.cleanup) 10⟩
  let ip : Σ q,Program (permanentTapes (10+s) c+10) q 2 :=
    ⟨_,extend (CompactComplexControllerAlignedCommit.program (s:=s) (c:=c)) 10⟩
  have h0 := compose_runs pp (family (s:=s) (c:=c)) hp hf
  have h1 := compose_runs (compose pp (family (s:=s) (c:=c))) cp h0 hclean
  have h := compose_runs (compose (compose pp (family (s:=s) (c:=c))) cp) ip h1 hcommit
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz) (by dsimp only [V]; omega)


open ButterflyStreamData (Coefficient)
open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision (BoundedGrid)

/-- Literal unchanged-width coefficient contraction installed by the machine. -/
def contracted {N : ℕ} (gap : ℕ) (f : Fin N → Coefficient) (i : Fin N) : Coefficient :=
  (NativeSignedGapScan.result gap (f i).1,NativeSignedGapScan.result gap (f i).2)

private theorem fields_contract (cs : List Coefficient) (gap : ℕ) :
    (NativeSignedReturnPrecision.fields cs).map (NativeSignedGapScan.result gap)=
      NativeSignedReturnPrecision.fields
        (cs.map (fun x => (NativeSignedGapScan.result gap x.1,NativeSignedGapScan.result gap x.2))) := by
  induction cs with
  | nil => rfl
  | cons x cs ih =>
    simpa only [NativeSignedReturnPrecision.fields,List.flatMap_cons,List.map_cons,List.map_nil,
      List.map_append,List.cons_append,List.nil_append] using congrArg (fun ys =>
        NativeSignedGapScan.result gap x.1::NativeSignedGapScan.result gap x.2::ys) ih

/-- The physical emitted field list is exactly the contracted coefficient
array, including both components and original coefficient ordering. -/
theorem words_contracted {N : ℕ} (f : Fin N → Coefficient) (gap : ℕ) :
    (CompactComplexStoppedGridHandoff.words f).map (NativeSignedGapScan.result gap)=
      CompactComplexStoppedGridHandoff.words (contracted gap f) := by
  rw [CompactComplexStoppedGridHandoff.words,fields_contract,List.map_ofFn]
  rfl

/-- Each permanent role returns its contracted literal array at head zero. -/
theorem returned_role {N : ℕ} (f : Fin c → Fin N → Coefficient)
    (current target : ℕ) (payload : Tapes (1+c) 2) (j : Fin c) :
    (returned (fun r => CompactComplexStoppedGridHandoff.words (f r)) current target payload).head (Fin.natAdd 1 j)=0 ∧
    (returned (fun r => CompactComplexStoppedGridHandoff.words (f r)) current target payload).tape (Fin.natAdd 1 j)=
      word (CompactComplexStoppedGridHandoff.words (contracted (current-target) (f j))) := by
  have h := CompactComplexSpectatorRoleSchedule.execute_slot
    (fun r => word ((CompactComplexStoppedGridHandoff.words (f r)).map (NativeSignedGapScan.result (current-target))))
    (List.finRange c) payload j
  simpa only [returned,List.mem_finRange,ite_true,words_contracted] using h

/-- The original native source65 stream and head are framed by every role
contraction and by the subsequent denominator commit. -/
theorem returned_source (ws : Fin c → List Word) (current target : ℕ) (payload : Tapes (1+c) 2) :
    (returned ws current target payload).head 0=payload.head 0 ∧
    (returned ws current target payload).tape 0=payload.tape 0 :=
  CompactComplexSpectatorRoleSchedule.execute_source _ _ _

/-- A semantic coarser-grid certificate, not a signed-width reserve, justifies
exact signed division of every actual stored Gaussian coefficient. -/
theorem contracted_exact {N : ℕ} (f : Fin N → Coefficient) (b current target M : ℕ)
    (hle : target≤current) (hcapacity : current-target≤b+1)
    (hw : ∀ i,(f i).1.length=b+1 ∧ (f i).2.length=b+1)
    (hg : ∀ i,BoundedGrid target M
      (complexValue (signedValue b (f i).1) (signedValue b (f i).2) current)) :
    (∀ i,(contracted (current-target) f i).1.length=b+1 ∧
      (contracted (current-target) f i).2.length=b+1) ∧
    (∀ i,complexValue (signedValue b (contracted (current-target) f i).1)
      (signedValue b (contracted (current-target) f i).2) target=
      complexValue (signedValue b (f i).1) (signedValue b (f i).2) current) := by
  have h i := CompactComplexExactReturnFamily.field_exact b current target M (f i).1 (f i).2
    hle (hw i).1 (hw i).2 hcapacity (hg i)
  exact ⟨fun i => ⟨(h i).1,(h i).2.1⟩,fun i => (h i).2.2⟩

/-- Genuine completed-network correctness supplies the coarser return grid.
The equality below is the recursive execution interface; it is not inferred
from field width or from a retained target header. -/
theorem nonleaf_grid {N : ℕ} (f : Fin c → Fin N → Coefficient) (b current n k M : ℕ)
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin N → Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue (signedValue b (f j i).1) (signedValue b (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i)) :
    ∀ j i,BoundedGrid (CompactComplexDenominatorPolicy.networkTarget n k)
      (M*4^(2*CompactComplexRecursiveGeometry.arity^(k+1)))
      (complexValue (signedValue b (f j i).1) (signedValue b (f j i).2) current) := by
  intro j i
  rw [hcompleted]
  exact CompactComplexDenominatorPolicy.network_grid n k M original hg (roles j) (addresses i)

/-- A completed nonleaf's actual semantic exchange and completed live ledger
justify all physical contractions at its genuine return target. -/
theorem nonleaf_exact {N : ℕ} (f : Fin c → Fin N → Coefficient) (b current n k M : ℕ)
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin N → Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue (signedValue b (f j i).1) (signedValue b (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i))
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hcapacity : current-CompactComplexDenominatorPolicy.networkTarget n k≤b+1)
    (hw : ∀ j i,(f j i).1.length=b+1 ∧ (f j i).2.length=b+1) :
    ∀ j,(∀ i,(contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1.length=b+1 ∧
      (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2.length=b+1) ∧
    (∀ i,complexValue
      (signedValue b (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1)
      (signedValue b (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      complexValue (signedValue b (f j i).1) (signedValue b (f j i).2) current) := by
  have hgrid := nonleaf_grid f b current n k M roles addresses original hg hcompleted
  intro j
  exact contracted_exact (f j) b current _ _
    (CompactComplexDenominatorPolicy.network_target_le_current n k current hledger) hcapacity (hw j) (hgrid j)

/-- End-to-end return for the real completed nonleaf interface. Original raw
headers produce the physical length word; semantic network correctness supplies
coarser-grid divisibility, while the actual completed ledger supplies the target
ordering. Full recursive execution must still establish those two interfaces. -/
theorem nonleaf_runs (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current n k M : ℕ)
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hcapacity : current-(CompactComplexDenominatorPolicy.networkTarget n k)≤CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits (CompactComplexDenominatorPolicy.networkTarget n k)))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size (roleRows headerCount rows merge) sh.bits (2^ell)) →
      Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i)) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    Realizes (program (s:=s) (c:=c) headerCount merge)
      (bank control queue scalar old tail storage payload)
      (bank control queue scalar old tail (committed storage (CompactComplexDenominatorPolicy.networkTarget n k)) (returned ws current (CompactComplexDenominatorPolicy.networkTarget n k) payload))
      (ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
        c*(129*streamVolume sh headerCount rows ell metadataP merge+8*current+360)+
        ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup prepared+
        (2*(bits current).length+4*(bits (CompactComplexDenominatorPolicy.networkTarget n k)).length+15)+3) ∧
    ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i) := by
  dsimp only
  have horder := CompactComplexDenominatorPolicy.network_target_le_current n k current hledger
  have hrun := raw_runs sh headerCount rows ell metadataP merge hcount hr hgroup hG hA hK hmetadata
    rho left count slots right src dst control queue scalar tail storage payload f hw current
    (CompactComplexDenominatorPolicy.networkTarget n k) horder hcapacity hc ht hs
  have hwidth : ∀ j i,(f j i).1.length=CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 ∧
      (f j i).2.length=CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+1 := by
    intro j i
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw j i
  have hexact := nonleaf_exact f (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
    current n k M roles addresses original hg hcompleted hledger hcapacity hwidth
  exact ⟨hrun,fun j i => ((hexact j).2 i).trans (hcompleted j i)⟩

end
end IntegerMultBounds.Machine.CompactComplexControllerExactReturn

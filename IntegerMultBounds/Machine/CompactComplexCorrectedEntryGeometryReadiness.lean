import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedEntryTablePath
import IntegerMultBounds.Machine.NativeEndpointCharacterPath

/-! Literal reached-bank facts after corrected tag2. Original raw geometry,
including payload descriptor5, is retained; scalar coefficient arrays are
exposed directly without full-stage record-capacity assumptions. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedEntryGeometryReadiness
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSourceReadyScalarChildReadiness (entryBank entry_prefix)
open CompactComplexSpectatorTargetBank (roleSlot oldSlot)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] roleCount

def data (v : Stage sh) (hslots : v.slots=arity) (rows ell p : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell) :=
  NativeEndpointCharacterNamedBank.data false v hslots ell p
    (NativeEndpointCharacterEntryRoles.data rows ell hd f)

/-- The same physical corrected role, with the original quotient cardinality. -/
def array (v : Stage sh) (hslots : v.slots=arity) (rows ell p : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell) (j : Fin roleCount) : Array sh (rows/roleCount) ell :=
  fun i => data v hslots rows ell p hd f (roleEncoding.symm j)
    (Fin.cast (NativeEndpointCharacterEntryRoles.cardinality sh rows ell).symm i)

private theorem word_cast {N M : ℕ} (h : N=M) (f : Fin M → ButterflyStreamData.Coefficient) :
    NativeZeroPaddingArray.word (fun i => f (Fin.cast h i))=NativeZeroPaddingArray.word f := by
  subst M
  rfl

theorem array_word (v : Stage sh) (hslots : v.slots=arity) (rows ell p : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell) (j : Fin roleCount) :
    NativeZeroPaddingArray.word (array v hslots rows ell p hd f j)=
      NativeZeroPaddingArray.word (data v hslots rows ell p hd f (roleEncoding.symm j)) := by
  unfold array
  exact word_cast (NativeEndpointCharacterEntryRoles.cardinality sh rows ell).symm _

theorem data_width (v : Stage sh) (hslots : v.slots=arity) (rows ell p : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    ∀ a i,(data v hslots rows ell p hd f a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data v hslots rows ell p hd f a i).2.length=CompactNativeRoleHeaders.recordWidth sh p := by
  intro a i
  cases a with
  | inl b =>
    exact NativeEndpointCharacterPath.width false v hslots ell p
      (NativeEndpointCharacterEntryRoles.data rows ell hd f) b _
      (NativeEndpointCharacterEntryRoles.width rows ell p hd f hw _) i
  | inr a =>
    exact NativeEndpointCharacterEntryRoles.width rows ell p hd f hw _ i

theorem array_width (v : Stage sh) (hslots : v.slots=arity) (rows ell p : ℕ)
    (hd : roleCount∣rows) (f : Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    ∀ j i,(array v hslots rows ell p hd f j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (array v hslots rows ell p hd f j i).2.length=CompactNativeRoleHeaders.recordWidth sh p :=
  fun _ _ => data_width v hslots rows ell p hd f hw _ _

def storage (old : Tapes (10+s) 2) (target : ℕ) :=
  NativeEndpointCharacterEntryStorage.storage old target

theorem storage_other (old : Tapes (10+s) 2) (target : ℕ) (i : Fin (10+s)) (hi : i.val≠8) :
    (storage old target).head i=old.head i ∧ (storage old target).tape i=old.tape i := by
  have hn : i≠(⟨8,by omega⟩ : Fin (10+s)) := by intro h; exact hi (congrArg Fin.val h)
  simp only [storage,NativeEndpointCharacterEntryStorage.storage,SharedPlacementAlphabet.setTape,
    Function.update_of_ne hn,and_self]

theorem storage_target (old : Tapes (10+s) 2) (target : ℕ) :
    (storage old target).head ⟨8,by omega⟩=1 ∧
      (storage old target).tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target) := by
  simp only [storage,NativeEndpointCharacterEntryStorage.storage,SharedPlacementAlphabet.setTape,
    Function.update_self,and_self]

theorem storage_live (old : Tapes (10+s) 2) (target n : ℕ)
    (hn : old.head ⟨7,by omega⟩=1 ∧ old.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n)) :
    (storage old target).head ⟨7,by omega⟩=1 ∧
      (storage old target).tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n) := by
  have h := storage_other old target (⟨7,by omega⟩ : Fin (10+s)) (by simp)
  exact ⟨h.1.trans hn.1,h.2.trans hn.2⟩

theorem storage_count_blank (old : Tapes (10+s) 2) (target : ℕ)
    (hblank : old.head ⟨0,by omega⟩=0 ∧ old.tape ⟨0,by omega⟩=(fun _ => blank)) :
    (storage old target).head ⟨0,by omega⟩=0 ∧
      (storage old target).tape ⟨0,by omega⟩=(fun _ => blank) := by
  have h := storage_other old target (⟨0,by omega⟩ : Fin (10+s)) (by simp)
  exact ⟨h.1.trans hblank.1,h.2.trans hblank.2⟩

theorem storage_ancestor (old : Tapes (10+s) 2) (target : ℕ) (i : Fin s) :
    (storage old target).head (Fin.natAdd 10 i)=old.head (Fin.natAdd 10 i) ∧
      (storage old target).tape (Fin.natAdd 10 i)=old.tape (Fin.natAdd 10 i) :=
  storage_other old target _ (by simp only [Fin.val_natAdd]; omega)

private theorem entry_append {c : ℕ} (base : Tapes (permanentTapes (10+s) c) 2) (aux : Tapes 2 2)
    (frame : Tapes 7 2) :
    CompactComplexNonleafSpectatorTargetRestore.entry base (aux.append frame)=
      (entryBank base aux).append frame := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m:=permanentTapes (10+s) c+2) (n:=7) with
  | left i =>
    induction i using Fin.addCases (m:=permanentTapes (10+s) c) (n:=2) with
    | left i =>
      have hi : CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
          (Fin.castAdd 7 (Fin.castAdd 2 i))=Fin.castAdd 9 i := Fin.ext rfl
      simp only [Equiv.symm_symm,hi,entryBank,Tapes.append,Fin.addCases_left]
    | right i =>
      have hi : CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
          (Fin.castAdd 7 (Fin.natAdd (permanentTapes (10+s) c) i))=
          Fin.natAdd (permanentTapes (10+s) c) (Fin.castAdd 7 i) := Fin.ext rfl
      simp only [Equiv.symm_symm,hi,entryBank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i =>
    have hi : CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c
        (Fin.natAdd (permanentTapes (10+s) c+2) i)=
        Fin.natAdd (permanentTapes (10+s) c) (Fin.natAdd 2 i) := by
      apply Fin.ext
      change permanentTapes (10+s) c+2+i.val=permanentTapes (10+s) c+(2+i.val)
      omega
    simp only [Equiv.symm_symm,hi,Tapes.append,Fin.addCases_right]

section Caller
variable (v : Stage sh) (hslots : v.slots=arity) (rows ell p n k : ℕ)
variable (hd : roleCount∣rows) (f : Array sh rows ell)
variable (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
variable (tail : Tapes 22 2) (old : Tapes (10+s) 2) (aux : Tapes 2 2)

def permanent := bank control queue scalar (CompactComplexNativeCodec.raw v rows ell p) tail
  (storage old (n+2*arity^(k+1)))
  (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data v hslots rows ell p hd f))

def caller := entryBank (permanent v hslots rows ell p n k hd f control queue scalar tail old) aux

/-- Exactly the full bank returned by the checked corrected tag2 execution. -/
def full (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :=
  (CompactComplexSourceReadyNonleafContraction.ready
    (permanent v hslots rows ell p n k hd f control queue scalar tail old)
    (aux.append (SharedBank.empty 7 2))
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append scratch

/-- Exact caller bank inside the corrected public child frame. -/
theorem entry_eq_caller :
    CompactComplexNonleafSpectatorTargetRestore.entry
      (permanent v hslots rows ell p n k hd f control queue scalar tail old)
      (aux.append (SharedBank.empty 7 2))=
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).append (SharedBank.empty 7 2) :=
  entry_append _ _ _

theorem full_eq_caller (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    full v hslots rows ell p n k hd f control queue scalar tail old aux scratch=
      (CompactComplexSourceReadyWorkspace.ready
        ((caller v hslots rows ell p n k hd f control queue scalar tail old aux).append
          (SharedBank.empty 7 2))).append scratch := by
  unfold full CompactComplexSourceReadyNonleafContraction.ready
  rw [entry_eq_caller]
  rfl

theorem caller_raw :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (caller v hslots rows ell p n k hd f control queue scalar tail old aux)=
      ActiveRepairRankHeadersCommands.bank (CompactComplexNativeCodec.raw v rows ell p) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_headers _ _ _ _ _ _ _ _

theorem caller_role (j : Fin roleCount) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleEntry.roleTape j)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word (array v hslots rows ell p hd f j)) := by
  have he := entry_prefix (permanent v hslots rows ell p n k hd f control queue scalar tail old) aux (roleSlot j)
  have hb := CompactComplexSpectatorTargetBank.role_bank control queue scalar
    (CompactComplexNativeCodec.raw v rows ell p) tail (storage old (n+2*arity^(k+1)))
    (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data v hslots rows ell p hd f)) j
  have hp : (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
      (data v hslots rows ell p hd f)).head (Fin.natAdd 1 j)=0 ∧
    (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
      (data v hslots rows ell p hd f)).tape (Fin.natAdd 1 j)=
      NativeZeroPadding.word (NativeZeroPaddingArray.word (data v hslots rows ell p hd f (roleEncoding.symm j))) := by
    simp only [CompactComplexEndpointRoleExchange.payload,CyclicRowCopy.payload,Tapes.append,
      Fin.addCases_right,and_self]
  exact ⟨he.1.trans (hb.1.trans hp.1),
    he.2.trans (hb.2.trans (hp.2.trans (congrArg NativeZeroPadding.word (array_word v hslots rows ell p hd f j).symm)))⟩

theorem caller_storage (i : Fin (10+s)) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot i)=(storage old (n+2*arity^(k+1))).head i ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot i)=(storage old (n+2*arity^(k+1))).tape i := by
  have he := entry_prefix (permanent v hslots rows ell p n k hd f control queue scalar tail old) aux (oldSlot i)
  have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar
    (CompactComplexNativeCodec.raw v rows ell p) tail (storage old (n+2*arity^(k+1)))
    (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data v hslots rows ell p hd f)) i
  exact ⟨he.1.trans hb.1,he.2.trans hb.2⟩

theorem caller_target :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=1 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩)=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))) := by
  have hc := caller_storage v hslots rows ell p n k hd f control queue scalar tail old aux ⟨8,by omega⟩
  have hs := storage_target old (n+2*arity^(k+1))
  exact ⟨hc.1.trans hs.1,hc.2.trans hs.2⟩

theorem caller_live (hn : old.head ⟨7,by omega⟩=1 ∧
    old.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n)) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=1 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩)=RadixZeroFill.encodedBinary (bits n) := by
  have hc := caller_storage v hslots rows ell p n k hd f control queue scalar tail old aux ⟨7,by omega⟩
  have hs := storage_live old (n+2*arity^(k+1)) n hn
  exact ⟨hc.1.trans hs.1,hc.2.trans hs.2⟩

theorem caller_count_blank (hblank : old.head ⟨0,by omega⟩=0 ∧ old.tape ⟨0,by omega⟩=(fun _ => blank)) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨0,by omega⟩)=0 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot ⟨0,by omega⟩)=(fun _ => blank) := by
  have hc := caller_storage v hslots rows ell p n k hd f control queue scalar tail old aux ⟨0,by omega⟩
  have hs := storage_count_blank old (n+2*arity^(k+1)) hblank
  exact ⟨hc.1.trans hs.1,hc.2.trans hs.2⟩

theorem caller_ancestor (i : Fin s) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 i))=old.head (Fin.natAdd 10 i) ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 i))=old.tape (Fin.natAdd 10 i) := by
  have hc := caller_storage v hslots rows ell p n k hd f control queue scalar tail old aux (Fin.natAdd 10 i)
  have hs := storage_ancestor old (n+2*arity^(k+1)) i
  exact ⟨hc.1.trans hs.1,hc.2.trans hs.2⟩

theorem caller_source :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head
      CompactComplexNonleafRoleEntry.source=0 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      CompactComplexNonleafRoleEntry.source=(fun _ => blank) := by
  have he := entry_prefix (permanent v hslots rows ell p n k hd f control queue scalar tail old) aux
    (CompactComplexSpectatorTargetBank.numericSlot 65)
  have hb := CompactComplexSourceReadyPrefixReadiness.source_bank control queue scalar
    (CompactComplexNativeCodec.raw v rows ell p) tail (storage old (n+2*arity^(k+1)))
    (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0 (data v hslots rows ell p hd f))
  have hp : (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
      (data v hslots rows ell p hd f)).head 0=0 ∧
    (CompactComplexEndpointRoleExchange.payload (fun _ => blank) 0
      (data v hslots rows ell p hd f)).tape 0=(fun _ => blank) := by
    constructor <;> rfl
  exact ⟨he.1.trans (hb.1.trans hp.1),he.2.trans (hb.2.trans hp.2)⟩

theorem caller_source_supported (volume : ℕ) :
    RoleArrayStack.Supported ((caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      CompactComplexNonleafRoleEntry.source) volume := by
  rw [(caller_source v hslots rows ell p n k hd f control queue scalar tail old aux).2]
  intro z hz
  rfl

theorem caller_role_supported
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p) (j : Fin roleCount) :
    RoleArrayStack.Supported ((caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape
      (CompactComplexNonleafRoleEntry.roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
  rw [(caller_role v hslots rows ell p n k hd f control queue scalar tail old aux j).2]
  apply RoleArrayStack.supported_word
  have hw' := array_width v hslots rows ell p hd f hw j
  have hh := CyclicRowSplit.prefix_length
    (fun i => ButterflyStreamData.encoded (array v hslots rows ell p hd f j i))
    (2*(CompactNativeRoleHeaders.recordWidth sh p+1))
    (fun i => DelimitedRadixRecord.complex_length _ _ _ (hw' i).1 (hw' i).2)
    (ButterflySpectatorGeometry.Size (rows/roleCount) sh.bits (2^ell)) le_rfl
  rw [CyclicRowCycle.prefix_all] at hh
  change (NativeZeroPaddingArray.word (array v hslots rows ell p hd f j)).length ≤ _
  change (NativeZeroPaddingArray.word (array v hslots rows ell p hd f j)).length=_ at hh
  rw [hh]
  simp only [CompactComplexSpectatorVolumeHeaders.streamVolume,
    CompactComplexSpectatorVolumeHeaders.roleRows,ite_true,ButterflySpectatorGeometry.Size]
  exact le_of_eq (by ring)

theorem caller_exponent (e : ℕ)
    (he : control.head 1=1 ∧ control.tape 1=BinaryDescriptorStack.descriptor (bits e))
    (h28 : control.head 28=0 ∧ control.tape 28=(fun _ => blank))
    (h29 : control.head 29=0 ∧ control.tape 29=(fun _ => blank)) :
    Placement.active CompactComplexNonleafRoleChildBank.exponentPlacement
      ((caller v hslots rows ell p n k hd f control queue scalar tail old aux).append (SharedBank.empty 7 2))=
      CompactComplexExponentStep.bank e :=
  CompactComplexSourceReadyScalarChildReadiness.entry_exponent _ _ _ _ _ _ _ _ _ e he h28 h29

theorem caller_clock (hclock : aux.head 1=0 ∧ aux.tape 1=(fun _ => blank)) :
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).head CompactComplexNonleafRoleEntry.clock=0 ∧
    (caller v hslots rows ell p n k hd f control queue scalar tail old aux).tape CompactComplexNonleafRoleEntry.clock=(fun _ => blank) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_clock _ aux hclock

theorem caller_free (hfree : CompactComplexSourceReadyPrefixReadiness.BlankAfter aux 0)
    (selected : Fin roleCount) (masterVolume roleVolume : ℕ) :
    CompactComplexNonleafRoleReturn.Free selected masterVolume roleVolume
      (caller v hslots rows ell p n k hd f control queue scalar tail old aux) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_free _ aux hfree selected masterVolume roleVolume

end Caller
end
end IntegerMultBounds.Machine.CompactComplexCorrectedEntryGeometryReadiness

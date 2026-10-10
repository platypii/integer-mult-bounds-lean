import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafScalarInitialReadiness
import IntegerMultBounds.Machine.CompactNativeRoleRecombine

/-! Arbitrary corrected physical role families supply the canonical scalar
prefix inputs directly. Recombination and original named-role identities derive
all source words, widths and decoded grids while retaining raw/live/stack data. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedScalarReadiness
noncomputable section
open ButterflyStreamData (Coefficient)
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexScalarIntegerRows (wireIndex Wire)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexSourceReadyNonleafScalarInitialReadiness (polynomial polynomial_width)
open CompactComplexSourceReadyPrefixGeometry (cardinality)
variable {sh : Shape}

/-- Canonical grouping reads each corrected role at its actual named port. -/
def xs (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows/roleCount) (data : Fin roleCount → Array sh (rows/roleCount) ell) :
    Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient :=
  fun a => polynomial inp (rows/roleCount) ell hrows (data (roleIndex a))

/-- This is the original canonical decoder applied to the unique recombined
corrected array; no new serialization or source interpretation is introduced. -/
theorem xs_recombine (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (data : Fin roleCount → Array sh (rows/roleCount) ell) :
    CompactComplexSourceReadyNonleafScalarInitialReadiness.xs inp rows ell hrows hd
      (CompactNativeRoleRecombine.recombine sh rows roleCount ell hd data)=xs inp rows ell hrows data := by
  funext a
  unfold CompactComplexSourceReadyNonleafScalarInitialReadiness.xs xs
  rw [CompactNativeRoleRecombine.role_recombine]

theorem xs_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows/roleCount) (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w) :
    ∀ a i j,(xs inp rows ell hrows data a i j).1.length=w ∧
      (xs inp rows ell hrows data a i j).2.length=w :=
  fun a => polynomial_width inp (rows/roleCount) ell w hrows _ (hw (roleIndex a))

theorem xs_array (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows/roleCount) (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (a : Fin wireCount) :
    CompactComplexSourceReadyPrefixGeometry.array inp (rows/roleCount) ell hrows (xs inp rows ell hrows data a)=
      data (roleIndex a) :=
  CompactComplexSourceReadyNonleafScalarInitialReadiness.array_polynomial inp (rows/roleCount) ell hrows _

def payload (data : Fin roleCount → Array sh (rows/roleCount) ell) : Tapes (1+roleCount) 2 :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data j))) 0 (fun _ => 0)

theorem payload_recombine (rows ell : ℕ) (hd : roleCount ∣ rows)
    (data : Fin roleCount → Array sh (rows/roleCount) ell) :
    CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd
      (CompactNativeRoleRecombine.recombine sh rows roleCount ell hd data)=payload data :=
  CompactNativeRoleRecombine.rolePayload sh rows roleCount ell hd data

/-- Exact numerical scalar decoding at the original named corrected role. -/
theorem xs_decode (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n : ℕ)
    (hrows : inp.rows=rows/roleCount) (hp : 2*sh.bits≤p)
    (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (i : Fin (ActivePrefixStageTripleWords.count inp*2^ell)) (wire : Wire) :
    CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) n
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows data a)) i wire=
    CompactSpectatorInheritedGrid.decoded sh (rows/roleCount) ell (p-2*sh.bits) n
      (data (roleEncoding wire)) (Fin.cast (cardinality inp (rows/roleCount) ell hrows) i) := by
  unfold CompactComplexScalarSequenceSemantics.values
  dsimp only
  rw [show ActivePrefixStageNativePolynomial.flattenArray
    (xs inp rows ell hrows data (wireIndex wire))=_ from
    CompactComplexSourceReadyNonleafScalarInitialReadiness.flatten_polynomial inp (rows/roleCount) ell hrows _]
  unfold CompactSpectatorInheritedGrid.decoded ButterflyStreamSemantics.decode
  rw [CompactComplexSourceReadyPrefixGeometry.retained_half p hp]
  simp only [roleIndex,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem xs_grid (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n M : ℕ)
    (hrows : inp.rows=rows/roleCount) (hp : 2*sh.bits≤p)
    (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (hg : ∀ a,CompactSpectatorInheritedGrid.Grid sh (rows/roleCount) ell (p-2*sh.bits) n M (data a)) :
    ∀ i wire,Networks.GaussianPrecision.BoundedGrid n M
      (CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows data a)) i wire) := by
  intro i wire
  rw [xs_decode inp rows ell p n hrows hp data i wire]
  exact hg _ _

section Caller
variable {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
variable (hrows : inp.rows=rows/roleCount) (data : Fin roleCount → Array sh (rows/roleCount) ell)
variable (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w)
variable (control : Tapes 43 2) (queue : Tapes 1 2)
variable (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)

theorem caller_source (a : Fin wireCount) :
    let v := bank control queue scalar stage tail storage (payload data)
    v.head (CompactComplexSpectatorTargetBank.roleSlot (roleIndex a))=0 ∧
    v.tape (CompactComplexSpectatorTargetBank.roleSlot (roleIndex a))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp (xs inp rows ell hrows data a)
          (xs_width inp rows ell w hrows data hw a)))) := by
  dsimp only
  have hb := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage (payload data) (roleIndex a)
  have he := CompactComplexSourceReadyPrefixGeometry.array_word inp (rows/roleCount) ell w hrows
    (xs inp rows ell hrows data a) (xs_width inp rows ell w hrows data hw a)
  rw [xs_array] at he
  have hp : (payload data).head (Fin.natAdd 1 (roleIndex a))=0 ∧
      (payload data).tape (Fin.natAdd 1 (roleIndex a))=NativeZeroPadding.word
        (NativeZeroPaddingArray.word (data (roleIndex a))) := by
    simp only [payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right,and_self]
  exact ⟨hb.1.trans hp.1,hb.2.trans (hp.2.trans he)⟩

include hrows hw in
/-- The actual corrected payload supplies scalar Ready after physical count
construction; live7 is taken from the untouched storage bank. -/
theorem scalar_ready (hs : 7<s) (header : Fin s) (hh : header.val≠7) (d : ℕ)
    (hlive : storage.head ⟨7,hs⟩=1 ∧
      storage.tape ⟨7,hs⟩=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    let v := bank control queue scalar stage tail storage (payload data)
    CompactComplexScalarRolePorts.Ready (s:=s+43) (by omega) (Fin.castAdd 43 header)
      (CompactComplexScalarCountRootBank.output header v (inp.rows*2^sh.bits*2^ell))
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows data a)) d := by
  dsimp only
  apply CompactComplexScalarCountRootBank.scalar_ready inp hs header hh _
    (xs inp rows ell hrows data) (xs_width inp rows ell w hrows data hw) d
  · exact caller_source inp rows ell w hrows data hw control queue scalar stage tail storage
  · have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage (payload data) ⟨7,hs⟩
    exact ⟨hb.1.trans hlive.1,hb.2.trans hlive.2⟩

include hrows hw in
/-- Direct Ready at the actual recombined rolePayload endpoint supplied by
correction loops, with no source-word equality among the premises. -/
theorem recombined_scalar_ready (hd : roleCount ∣ rows)
    (hs : 7<s) (header : Fin s) (hh : header.val≠7) (d : ℕ)
    (hlive : storage.head ⟨7,hs⟩=1 ∧
      storage.tape ⟨7,hs⟩=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    let v := bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd
        (CompactNativeRoleRecombine.recombine sh rows roleCount ell hd data))
    CompactComplexScalarRolePorts.Ready (s:=s+43) (by omega) (Fin.castAdd 43 header)
      (CompactComplexScalarCountRootBank.output header v (inp.rows*2^sh.bits*2^ell))
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows data a)) d := by
  rw [payload_recombine]
  exact scalar_ready inp rows ell w hrows data hw control queue scalar stage tail storage hs header hh d hlive

end Caller

/-- All corrected role streams have exact generated role-volume support. -/
theorem caller_roles {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hrows : inp.rows=rows/roleCount) (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (data a i).2.length=ButterflyGuard.halfWidth p sh.bits+1)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2) :
    let v := bank control queue scalar stage tail storage (payload data)
    ∀ j,v.head (CompactComplexSpectatorTargetBank.roleSlot j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexSpectatorTargetBank.roleSlot j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
  dsimp only
  intro j
  have hs := caller_source inp rows ell _ hrows data hw control queue scalar stage tail storage (roleIndex.symm j)
  simp only [Equiv.apply_symm_apply] at hs
  refine ⟨hs.1,?_⟩
  rw [hs.2,←CompactComplexSourceReadyPrefixReadiness.native_role_volume inp rows ell p roleCount hrows]
  apply RoleArrayStack.supported_word
  simp only [List.length_ofFn]
  exact le_rfl

/-- Parent raw geometry is unchanged, including its original parent row count. -/
theorem caller_raw {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (aux : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (CompactComplexSourceReadyScalarChildReadiness.entryBank
        (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage rows ell p) tail storage (payload data)) aux)=
      ActiveRepairRankHeadersCommands.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p inp.stage.rho inp.stage.left inp.stage.f
          inp.stage.slots inp.stage.right inp.stage.source.val inp.stage.target.val) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_headers _ _ _ _ _ _ _ _

/-- Live7, target8 and every ancestor stack retain their whole words and heads. -/
theorem caller_storage {s : ℕ} (rows ell : ℕ) (data : Fin roleCount → Array sh (rows/roleCount) ell)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (i : Fin s) :
    (bank control queue scalar stage tail storage (payload data)).head (CompactComplexSpectatorTargetBank.oldSlot i)=storage.head i ∧
    (bank control queue scalar stage tail storage (payload data)).tape (CompactComplexSpectatorTargetBank.oldSlot i)=storage.tape i :=
  CompactComplexSpectatorTargetBank.old_bank _ _ _ _ _ _ _ _

/-- Genuine parent stage supplies the quotient internally for corrected inputs. -/
def canonicalXs {left k : ℕ} (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (rows ell : ℕ) (hgroup : 0<rows/roleCount)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hrecord : sh.bits+1≤sh.payload)
    (data : Fin roleCount → Array sh (rows/roleCount) ell) :
    Fin wireCount → Fin (ActivePrefixStageTripleWords.count
      (CompactComplexSourceReadyScalarChildReadiness.canonicalInput
        rho visit hactive pair rows hgroup hG hGK hrecord)) → Fin (2^ell) → Coefficient :=
  xs (CompactComplexSourceReadyScalarChildReadiness.canonicalInput
    rho visit hactive pair rows hgroup hG hGK hrecord) rows ell rfl data

/-- Named correction arrays and scalar words use the very same original roles. -/
theorem named_decode (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n : ℕ)
    (hrows : inp.rows=rows/roleCount) (hp : 2*sh.bits≤p) (data : Wire → Array sh (rows/roleCount) ell)
    (i : Fin (ActivePrefixStageTripleWords.count inp*2^ell)) (wire : Wire) :
    CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) n
      (fun a => ActivePrefixStageNativePolynomial.flattenArray
        (xs inp rows ell hrows (fun j => data (roleEncoding.symm j)) a)) i wire=
      CompactSpectatorInheritedGrid.decoded sh (rows/roleCount) ell (p-2*sh.bits) n
        (data wire) (Fin.cast (cardinality inp (rows/roleCount) ell hrows) i) := by
  simpa only [Equiv.symm_apply_apply] using
    xs_decode inp rows ell p n hrows hp (fun j => data (roleEncoding.symm j)) i wire

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedScalarReadiness

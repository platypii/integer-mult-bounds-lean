import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarChildReadiness
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit

/-! Canonical initial scalar rows are read from the actual cyclic role split.
The reverse cardinality cast preserves the literal word and original numerical
decoder. Source correction is a separate subsequent operation. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafScalarInitialReadiness
noncomputable section
open ButterflyStreamData (Coefficient)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexSourceReadyPrefixGeometry (cardinality array)
open CompactComplexScalarNativeEndpoint (unflatten)
variable {sh : CompactGadgetReservationShape.Shape}

/-- Reverse grouping of an existing array, with no change of coefficient order. -/
def polynomial (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient :=
  unflatten (fun i => f (Fin.cast (cardinality inp rows ell hrows) i))

theorem flatten_polynomial (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    ActivePrefixStageNativePolynomial.flattenArray (polynomial inp rows ell hrows f)=
      fun i => f (Fin.cast (cardinality inp rows ell hrows) i) :=
  CompactComplexScalarNativeEndpoint.flatten_unflatten _

theorem array_polynomial (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    array inp rows ell hrows (polynomial inp rows ell hrows f)=f := by
  funext i
  unfold array
  rw [flatten_polynomial]
  exact congrArg f (Fin.ext rfl)

theorem polynomial_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ i j,(polynomial inp rows ell hrows f i j).1.length=w ∧
      (polynomial inp rows ell hrows f i j).2.length=w := fun _ _ => hw _

/-- Genuine role selection retains every original record width. -/
theorem role_width (rows c ell w : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) (j : Fin c) :
    ∀ i,(CompactNativeRoleReservedBridge.role sh rows c ell hd f j i).1.length=w ∧
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j i).2.length=w :=
  fun _ => hw _

/-- Named scalar inputs are the original physical roles, grouped into rows. -/
def xs (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient :=
  fun a => polynomial inp (rows/roleCount) ell hrows
    (CompactNativeRoleReservedBridge.role sh rows roleCount ell hd f (roleIndex a))

theorem xs_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) :
    ∀ a i j,(xs inp rows ell hrows hd f a i j).1.length=w ∧
      (xs inp rows ell hrows hd f a i j).2.length=w :=
  fun a => polynomial_width inp (rows/roleCount) ell w hrows _
    (role_width rows roleCount ell w hd f hw (roleIndex a))

theorem xs_array (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) (a : Fin wireCount) :
    array inp (rows/roleCount) ell hrows (xs inp rows ell hrows hd f a)=
      CompactNativeRoleReservedBridge.role sh rows roleCount ell hd f (roleIndex a) :=
  array_polynomial inp (rows/roleCount) ell hrows _

/-- Actual split payload supplies the native polynomial source word directly. -/
theorem payload_source (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w) (a : Fin wireCount) :
    let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f
    payload.head (Fin.natAdd 1 (roleIndex a))=0 ∧
    payload.tape (Fin.natAdd 1 (roleIndex a))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp (xs inp rows ell hrows hd f a)
          (xs_width inp rows ell w hrows hd f hw a)))) := by
  dsimp only
  have he := CompactComplexSourceReadyPrefixGeometry.array_word inp (rows/roleCount) ell w hrows
    (xs inp rows ell hrows hd f a) (xs_width inp rows ell w hrows hd f hw a)
  rw [xs_array] at he
  simpa only [CompactNativeRoleReservedBridge.rolePayload,CyclicRowCopy.payload,
    Tapes.append,Fin.addCases_right] using And.intro (rfl : (0 : ℤ)=0) he

/-- Original numerical grid survives the cyclic selection and reverse cast. -/
theorem role_grid (rows c ell q n M : ℕ) (hd : c ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n M f) (j : Fin c) :
    CompactSpectatorInheritedGrid.Grid sh (rows/c) ell q n M
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j) := fun _ => hg _

theorem xs_decode (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows) (hp : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (i : Fin (ActivePrefixStageTripleWords.count inp*2^ell))
    (wire : CompactComplexScalarIntegerRows.Wire) :
    CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) n
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows hd f a)) i wire=
    CompactSpectatorInheritedGrid.decoded sh (rows/roleCount) ell (p-2*sh.bits) n
      (CompactNativeRoleReservedBridge.role sh rows roleCount ell hd f (roleIndex
        (CompactComplexScalarIntegerRows.wireIndex wire)))
      (Fin.cast (cardinality inp (rows/roleCount) ell hrows) i) := by
  unfold CompactComplexScalarSequenceSemantics.values
  dsimp only
  rw [show ActivePrefixStageNativePolynomial.flattenArray
    (xs inp rows ell hrows hd f (CompactComplexScalarIntegerRows.wireIndex wire))=_ from
    flatten_polynomial inp (rows/roleCount) ell hrows _]
  unfold CompactSpectatorInheritedGrid.decoded ButterflyStreamSemantics.decode
  rw [CompactComplexSourceReadyPrefixGeometry.retained_half p hp]

theorem xs_grid (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n M : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows) (hp : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell (p-2*sh.bits) n M f) :
    ∀ i wire,Networks.GaussianPrecision.BoundedGrid n M
      (CompactComplexScalarSequenceSemantics.values (ButterflyGuard.halfWidth p sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows hd f a)) i wire) := by
  intro i wire
  rw [xs_decode inp rows ell p n hrows hd hp f i wire]
  exact role_grid rows roleCount ell (p-2*sh.bits) n M hd f hg _ _

section Caller
variable {s : ℕ}
variable (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
variable (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
variable (f : CompactSpectatorVisitGeometry.Array sh rows ell)
variable (hw : ∀ i,(f i).1.length=w ∧ (f i).2.length=w)
variable (control : Tapes 43 2) (queue : Tapes 1 2)
variable (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
variable (storage : Tapes s 2)

/-- Scalar source readiness on the actual permanent caller ports. -/
theorem caller_source (a : Fin wireCount) :
    let v := CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f)
    v.head (CompactComplexSpectatorTargetBank.roleSlot (roleIndex a))=0 ∧
    v.tape (CompactComplexSpectatorTargetBank.roleSlot (roleIndex a))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp (xs inp rows ell hrows hd f a)
          (xs_width inp rows ell w hrows hd f hw a)))) := by
  dsimp only
  have hb := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage
    (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f) (roleIndex a)
  have hp := payload_source inp rows ell w hrows hd f hw a
  exact ⟨hb.1.trans hp.1,hb.2.trans hp.2⟩

include hrows hw

/-- Physical role support comes from its real native serializer. -/
theorem caller_supported (a : Fin wireCount) :
    let v := CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f)
    RoleArrayStack.Supported (v.tape (CompactComplexSpectatorTargetBank.roleSlot (roleIndex a)))
      (ActivePrefixStageTripleWords.count inp*ActivePrefixStageNativePolynomial.symbols (2^ell) w) := by
  dsimp only
  rw [(caller_source inp rows ell w hrows hd f hw control queue scalar stage tail storage a).2]
  apply RoleArrayStack.supported_word
  simp only [List.length_ofFn]
  exact le_rfl

/-- Original role words and the separately retained live tape derive scalar
Ready after physical count setup; neither a prepared codec nor local Hoare is
an input. -/
theorem scalar_ready (hs : 7<s) (header : Fin s) (hh : header.val≠7) (d : ℕ)
    (hlive : storage.head ⟨7,hs⟩=1 ∧
      storage.tape ⟨7,hs⟩=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    let v := CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f)
    CompactComplexScalarRolePorts.Ready (s:=s+43) (by omega) (Fin.castAdd 43 header)
      (CompactComplexScalarCountRootBank.output header v (inp.rows*2^sh.bits*2^ell))
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs inp rows ell hrows hd f a)) d := by
  dsimp only
  apply CompactComplexScalarCountRootBank.scalar_ready inp hs header hh _
    (xs inp rows ell hrows hd f) (xs_width inp rows ell w hrows hd f hw) d
  · exact caller_source inp rows ell w hrows hd f hw control queue scalar stage tail storage
  · have hb := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f) ⟨7,hs⟩
    exact ⟨hb.1.trans hlive.1,hb.2.trans hlive.2⟩

end Caller

/-- Parent rows remain in the original raw metadata after role splitting;
only the scalar grouping uses the quotient. -/
theorem caller_raw {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hd : roleCount ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (aux : Tapes 2 2) :
    Placement.active CompactComplexNonleafRoleEntry.headerPlacement
      (CompactComplexSourceReadyScalarChildReadiness.entryBank
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw inp.stage rows ell p) tail storage
          (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f)) aux)=
      ActiveRepairRankHeadersCommands.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p inp.stage.rho inp.stage.left inp.stage.f
          inp.stage.slots inp.stage.right inp.stage.source.val inp.stage.target.val) :=
  CompactComplexSourceReadyScalarChildReadiness.entry_headers _ _ _ _ _ _ _ _

/-- Every actual split role has support at the physical role-volume header. -/
theorem caller_roles {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hrows : inp.rows=rows/roleCount) (hd : roleCount ∣ rows)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (f i).2.length=ButterflyGuard.halfWidth p sh.bits+1)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) :
    let v := CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
      (CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hd f)
    ∀ j,v.head (CompactComplexSpectatorTargetBank.roleSlot j)=0 ∧
      RoleArrayStack.Supported (v.tape (CompactComplexSpectatorTargetBank.roleSlot j))
        (CompactComplexSpectatorVolumeHeaders.streamVolume sh roleCount rows ell p true) := by
  dsimp only
  intro j
  have hh := (caller_source inp rows ell _ hrows hd f hw control queue scalar stage tail storage
    (roleIndex.symm j)).1
  have hv := caller_supported inp rows ell _ hrows hd f hw control queue scalar stage tail storage
    (roleIndex.symm j)
  rw [CompactComplexSourceReadyPrefixReadiness.native_role_volume inp rows ell p roleCount hrows] at hv
  simpa only [Equiv.apply_symm_apply] using And.intro hh hv

/-- Initial polynomials at the genuine enclosing parent stage. The quotient
and all retained stage geometry are constructed, rather than assumed. -/
def canonicalXs {left k : ℕ} (rho : Fin sh.chunk)
    (visit : CompactComplexRecursiveGeometry.Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin CompactComplexRecursiveGeometry.arity))
    (rows ell : ℕ) (hgroup : 0<rows/roleCount)
    (hG : 1≤sh.guard) (hGK : sh.guard+1≤sh.chunk) (hrecord : sh.bits+1≤sh.payload)
    (hd : roleCount ∣ rows) (f : CompactSpectatorVisitGeometry.Array sh rows ell) :
    Fin wireCount → Fin (ActivePrefixStageTripleWords.count
      (CompactComplexSourceReadyScalarChildReadiness.canonicalInput
        rho visit hactive pair rows hgroup hG hGK hrecord)) → Fin (2^ell) → Coefficient :=
  xs (CompactComplexSourceReadyScalarChildReadiness.canonicalInput
    rho visit hactive pair rows hgroup hG hGK hrecord) rows ell rfl hd f

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafScalarInitialReadiness

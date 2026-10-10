import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace

/-! Scalar count construction, actual role arithmetic and count erasure use
the original retained Stage and literal polynomial role arrays. No capacity
assumption from the full address-repair codec is needed, and the physical raw
payload descriptor is never replaced by an expanded codec shape. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryLifecycle
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexScalarCountRootBank (countSlot)
open CompactComplexScalarCountLifecycle (roleDivisor roleCost roleTimeConstant Realizes counted scalarOutput output)
open CompactComplexScalarIntegerRows (RowIndex)
open CompactComplexScalarRowBlock (wireCount)
open ButterflyStreamData (Coefficient)
open SharedBankStageInput (raw)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates
  roleCount CompactComplexScalarRolePorts.program CompactComplexScalarCountRootBank.roleProgram

/-- Physically generated count and unchanged literal role words give Ready.
The caller may contain any original geometry, including payload one. -/
theorem counted_ready {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (permanentTapes s roleCount) 2) (data : Fin wireCount → Fin n → Coefficient) (d : ℕ)
    (hsource : ∀ a,v.head (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      v.tape (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
        ButterflyStreamData.full (fun _ => blank) 0 (data a))
    (hlive : v.head (countSlot ⟨7,hs⟩)=1 ∧ v.tape (countSlot ⟨7,hs⟩)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    CompactComplexScalarRolePorts.Ready (CompactComplexScalarCountLifecycle.liveProof hs)
      (CompactComplexScalarCountLifecycle.storedHeader header) (counted header v n) data d := by
  refine ⟨?_,?_,?_⟩
  · intro a
    rw [CompactComplexScalarRolePorts.source_port]
    have hf := CompactComplexScalarCountRootBank.output_frame header v n _
      (CompactComplexScalarCountRootBank.role_ne_count header (CompactComplexScalarRolePorts.roleIndex a))
    exact ⟨hf.1.trans (hsource a).1,hf.2.trans (hsource a).2⟩
  · have hc := CompactComplexScalarCountRootBank.count_ready header v n
    simpa only [CompactComplexScalarRolePorts.count_port,CompactComplexScalarCountLifecycle.storedHeader,
      CompactComplexScalarCountRootBank.countSlot,counted] using hc
  · have hf := CompactComplexScalarCountRootBank.old_storage_frame header (⟨7,hs⟩ : Fin s) v n
      (by intro h; exact hh (congrArg Fin.val h).symm)
    have hl : (counted header v n).head (countSlot ⟨7,hs⟩)=1 ∧
        (counted header v n).tape (countSlot ⟨7,hs⟩)=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d) :=
      ⟨hf.1.trans hlive.1,hf.2.trans hlive.2⟩
    have hslot : Fin.castAdd 43 (⟨7,hs⟩ : Fin s)=
        (⟨7,CompactComplexScalarCountLifecycle.liveProof hs⟩ : Fin (s+43)) := Fin.ext rfl
    simpa only [CompactComplexScalarRolePorts.live_port,CompactComplexScalarCountRootBank.countSlot,
      hslot,counted] using hl


private theorem endpoint_count {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :
    (scalarOutput hs header v data d).head (countSlot header)=1 ∧
    (scalarOutput hs header v data d).tape (countSlot header)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n) := by
  have h := (CompactComplexScalarRolePorts.output_ready
    (CompactComplexScalarCountLifecycle.liveProof hs) (CompactComplexScalarCountLifecycle.storedHeader header)
    (CompactComplexScalarCountLifecycle.header_ne_live header hh) v data d).2.1
  simpa only [CompactComplexScalarRolePorts.count_port,scalarOutput,
    CompactComplexScalarCountLifecycle.storedHeader,CompactComplexScalarCountRootBank.countSlot] using h

/-- The literal polynomial arrays execute on the original stage bank; genuine
parent rows produce the role count, and the generated count is fully erased. -/
theorem role_runs {sh : Shape} (stage : Stage sh) (parentRows ell p : ℕ)
    (hrows : 0<parentRows/roleCount) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex) (w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
    (data : Fin wireCount → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload
    Realizes (CompactComplexScalarCountLifecycle.roleProgram hs header hh ops) v
      (output hs header v (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
      (roleCost ops (parentRows*2^sh.bits*2^ell) ((parentRows/roleCount)*(2^sh.bits*2^ell)) w d) := by
  dsimp only
  let v := bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload
  let n := (parentRows/roleCount)*(2^sh.bits*2^ell)
  have hparent : 0<parentRows := lt_of_lt_of_le hrows (Nat.div_le_self _ _)
  have hA := ActivePrefixStageParameters.positive_axes stage
  have h0 := CompactComplexScalarCountRootBank.role_runs roleDivisor header control queue scalar stage parentRows ell p
    tail storage payload (by rw [CompactComplexScalarCountLifecycle.roleDivisor_eq]; norm_num [roleCount])
    hparent hG hA hK hblank.1 hblank.2
  have hN : (parentRows/roleDivisor)*2^sh.bits*2^ell=n := by
    rw [CompactComplexScalarCountLifecycle.roleDivisor_eq,Nat.mul_assoc]
  rw [hN] at h0
  have hbanklive : v.head (countSlot ⟨7,hs⟩)=1 ∧
      v.tape (countSlot ⟨7,hs⟩)=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d) := by
    have he := CompactComplexScalarCountRootBank.count_bank ⟨7,hs⟩ control queue scalar
      (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload
    exact ⟨he.1.trans hlive.1,he.2.trans hlive.2⟩
  have hr := counted_ready hs header hh v data d hsource hbanklive
  have h1 := CompactComplexScalarRolePorts.runs (CompactComplexScalarCountLifecycle.liveProof hs)
    (CompactComplexScalarCountLifecycle.storedHeader header)
    (CompactComplexScalarCountLifecycle.header_ne_live header hh) ops (counted header v n) data w d hw hr
  have he := endpoint_count hs header hh (counted header v n)
    (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)
  have hn : 1≤n := Nat.succ_le_of_lt
    (Nat.mul_pos hrows (Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)))
  have h2 := CompactComplexScalarCountBudget.erase_runs_linear (countSlot header)
    (scalarOutput hs header (counted header v n)
      (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)) n hn he.2 he.1
  have h := CompactComplexScalarCountLifecycle.composed
    (k:=CompactComplexScalarCountLifecycle.publicTapes s) (x:=43)
    (y:=RawLinearCombinationComplexDenominatorPlaced.localCount wireCount
      CompactComplexScalarPolynomialSequence.scratch)
    (CompactComplexScalarCountLifecycle.roleSetupProgram header)
    (CompactComplexScalarCountLifecycle.scalarProgram hs header hh ops)
    (CompactComplexScalarCountLifecycle.eraseProgram header) v (counted header v n)
    (scalarOutput hs header (counted header v n)
      (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
    (output hs header v (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)) h0 h1 h2
  exact h.consequence (fun _ h => h) (fun _ h => h) (by simp only [roleCost,n,ButterflySpectatorGeometry.Size]; omega)

/-- The same physical endpoint has the original fixed linear-volume bound. -/
theorem role_runs_linear {sh : Shape} (stage : Stage sh) (parentRows ell p : ℕ)
    (hrows : 0<parentRows/roleCount) (hG : 0<sh.guard) (hK : 0<sh.chunk)
    (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex) (w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2)
    (data : Fin wireCount → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=w ∧ (data a i).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) (hd : d≤w) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell p) tail storage payload
    Realizes (CompactComplexScalarCountLifecycle.roleProgram hs header hh ops) v
      (output hs header v (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
      (roleTimeConstant ops*(parentRows*2^sh.bits*2^ell)*(w+1)) := by
  have h := role_runs stage parentRows ell p hrows hG hK hs header hh ops w d
    control queue scalar tail storage payload data hw hblank hsource hlive
  have hparent : 0<parentRows := lt_of_lt_of_le hrows (Nat.div_le_self _ _)
  have hn := (CompactComplexScalarCountBudget.count_bounds sh parentRows ell hparent).1
  have hcount : (parentRows/roleCount)*(2^sh.bits*2^ell)≤parentRows*2^sh.bits*2^ell := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (CompactComplexScalarCountLifecycle.role_cost_linear ops _ _ w d hn hcount hd)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryLifecycle

import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryLifecycle
import IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable
import IntegerMultBounds.Machine.CompactComplexScalarGroupProgress

/-! Genuine original grouped scalar events on the full source-ready fixed
node table on plain original geometry and literal role arrays, retaining the
next scalar-prefix grid and true live ledger. Payload one is permitted; the
physical raw descriptor is unchanged. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryEventPath
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCallerEndpoint (storageOutput emitted)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarSequenceSemantics (values)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactComplexRecursiveLiveProgress (Live liveSlot)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open Networks.GaussianPrecision (BoundedGrid)
open ButterflyStreamData (Coefficient)
open CompactComplexSourceReadyScalarWorkspace (roles tapes nodeTapes permanent ready output)
namespace Actual
export CompactComplexSourceReadyActualTable (countHeader countHeader_ne_live scalar event childReturn)
end Actual
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates
  Networks.ComplexFramedExecution.rows CompactComplexRolePhaseSite.roleCount
  CompactComplexCompletedLiveLower.schedule

private theorem liveProof : 7<10+s := by omega

/-- Literal emitted role words and the live-only storage update supply the
source and blank-count premises of the following actual scalar group. -/
theorem next_ready {sh : CompactGadgetReservationShape.Shape} (parentRows ell : ℕ) (hs : 7<10+s)
    (header : Fin (10+s)) (hh : header.val≠7)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar rawStage : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+roles) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array sh (parentRows/roles) ell) (n : ℕ)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank)) :
    let nextStorage := storageOutput hs storage n
    let nextPayload := emitted payload (fun j => CompactSpectatorLeafAxis.word
      (data (CompactComplexScalarRolePorts.roleIndex.symm j)))
    nextStorage.head header=0 ∧ nextStorage.tape header=(fun _ => blank) ∧
    ∀ a,(bank control queue scalar rawStage tail nextStorage nextPayload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar rawStage tail nextStorage nextPayload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a) := by
  dsimp only
  have hne : header≠(⟨7,hs⟩ : Fin (10+s)) := by
    intro he
    exact hh (congrArg Fin.val he)
  refine ⟨?_,?_,?_⟩
  · simpa only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_of_ne hne] using hblank.1
  · simpa only [storageOutput,SharedPlacementAlphabet.setTape,Function.update_of_ne hne] using hblank.2
  · intro a
    have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar rawStage tail
      (storageOutput hs storage n)
      (emitted payload (fun j => CompactSpectatorLeafAxis.word
        (data (CompactComplexScalarRolePorts.roleIndex.symm j))))
      (CompactComplexScalarRolePorts.roleIndex a)
    simpa only [emitted,Fin.addCases_right,Equiv.symm_apply_apply,
      CompactComplexSpectatorTargetBank.roleSlot] using h

theorem group_step {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (stage : ActivePrefixStageParameters.Stage sh) (parentRows : ℕ)
    (hrows : 0<parentRows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk) (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar
      (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array sh (parentRows/roles) ell)
    (hw : ∀ a i,(data a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head Actual.countHeader=0 ∧ storage.tape Actual.countHeader=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a))
    (hlive : storage.head ⟨7,liveProof (s:=s)⟩=1 ∧ storage.tape ⟨7,liveProof (s:=s)⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (baseline : ℕ) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (hledger : n≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows g.val).length)
    (hgrid : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        data i wire)) :
    let rawStage := CompactComplexNativeCodec.raw stage parentRows ell metadataP
    let next := execute (block g) data
    let nextStorage := storageOutput (liveProof (s:=s)) storage (n+(gates g).length)
    let nextPayload := emitted payload (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) data (CompactComplexScalarRolePorts.roleIndex.symm j)))
    let nextCaller := bank control queue scalar rawStage tail nextStorage nextPayload
    HoareTime (Actual.scalar (s:=s) g).2
      (fun z => z=ready v) (fun z => z=ready (output v nextCaller))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (parentRows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    (∀ a i,(next a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (next a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1) ∧
    (∀ i wire,BoundedGrid (n+(gates g).length)
      (CompactFramedScalarGrid.bound (g.val+1)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        next i wire)) ∧
    Live nextCaller (liveSlot (liveProof (s:=s))) (n+(gates g).length) ∧
    n+(gates g).length≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows (g.val+1)).length := by
  dsimp only
  let caller := bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP)
    tail storage payload
  have hused : (CompactFramedScalarGrid.rows g.val).length≤scalarRows :=
    CompactComplexDenominatorCapacity.actual_prefix g.val
  have hcapacity := CompactComplexDenominatorCapacity.target_capacity path scalarRows baseline
    (metadataP-2*sh.bits) (CompactFramedScalarGrid.rows g.val).length n n (by omega)
    hused hdenRoom hledger (by omega)
  have hfield : n≤ButterflyGuard.halfWidth metadataP sh.bits+1 := by
    unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at hcapacity
    unfold ButterflyGuard.halfWidth
    omega
  have hr := CompactComplexSourceReadyScalarGeometryLifecycle.role_runs_linear stage parentRows ell metadataP
    hrows hG hK (liveProof (s:=s)) Actual.countHeader Actual.countHeader_ne_live (block g)
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    data hw hblank hsource hlive hfield
  have hcaller := CompactComplexScalarCallerEndpoint.output_bank (liveProof (s:=s))
    Actual.countHeader Actual.countHeader_ne_live control queue scalar
    (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload
    (execute (block g) data) (n+(block g).length) hblank
  dsimp only at hr
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hr
  rw [←hv] at hr
  have hr' := CompactComplexSourceReadyScalarWorkspace.role_realizes (s:=s)
    Actual.countHeader Actual.countHeader_ne_live (block g) v _ hr
  have hw' := CompactComplexScalarLifecycleGrid.output_width (block g) data _ hw
  have hg' := CompactComplexScalarPrefixAdvance.group_grid path g data p C axes metadataP n
    ha hp haxes hroom hC hw hgrid
  have hl' := CompactComplexRecursiveLiveProgress.scalar_output_live (liveProof (s:=s))
    Actual.countHeader Actual.countHeader_ne_live caller (execute (block g) data) (n+(block g).length)
  dsimp only [caller] at hl'
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hl'
  have hb' := CompactComplexRecursiveLiveProgress.scalar_segment_bound baseline levels frames returned
    (CompactFramedScalarGrid.rows g.val).length n (block g) hledger
  rw [←CompactComplexScalarSegmentRows.prefix_length,CompactComplexScalarSegmentRows.block_length] at hb'
  exact ⟨hr',hw',hg',hl',hb'⟩

/-- The exact next denominator is physically present on the full caller,
including its added scalar suffix rather than only an abstract role array. -/
theorem output_live (v : Tapes (nodeTapes s roles) 2)
    (w : Tapes (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles) 2)
    (slot : Fin (CompactComplexSourceReadyScalarWorkspace.permanentTapes s roles)) (n : ℕ)
    (h : Live w slot n) :
    Live (ready (output v w))
      (Fin.castAdd CompactComplexSourceReadyScalarWorkspace.scratch
        (⟨slot.val,lt_of_lt_of_le slot.isLt CompactComplexSourceReadyScalarWorkspace.public_le⟩ :
          Fin (nodeTapes s roles))) n := by
  have he := CompactComplexSourceReadyScalarWorkspace.output_public v w slot
  change (ready (output v w)).head _=1 ∧ (ready (output v w)).tape _=_
  simp only [CompactComplexSourceReadyScalarWorkspace.ready,Tapes.append,Fin.addCases_left]
  exact ⟨he.1.trans h.1,he.2.trans h.2⟩

/-- The complete original serialized native record pays both coefficient
arithmetic and the real cyclic jump. -/
theorem coefficient_volume (sh : CompactGadgetReservationShape.Shape)
    (parentRows ell metadataP : ℕ) :
    (parentRows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)≤
      parentRows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth := by
  rw [NativePolynomialStageShape.volume]
  unfold ActivePrefixStageNativePolynomial.symbols NativePolynomialStageShape.width ButterflyGuard.width
  ring_nf
  omega

private theorem paid_join (C A V : ℕ) (hA : A≤V) (hV : 1≤V) :
    C*A+1≤(C+1)*V := by nlinarith

theorem scalar_path {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (stage : ActivePrefixStageParameters.Stage sh) (parentRows : ℕ)
    (hrows : 0<parentRows/roles) (hG : 0<sh.guard) (hK : 0<sh.chunk) (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar
      (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Array sh (parentRows/roles) ell)
    (hw : ∀ a i,(data a i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data a i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head Actual.countHeader=0 ∧ storage.tape Actual.countHeader=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          CompactSpectatorLeafAxis.word (data a))
    (hlive : storage.head ⟨7,liveProof (s:=s)⟩=1 ∧ storage.tape ⟨7,liveProof (s:=s)⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+(gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (baseline : ℕ) (hbase : baseline≤p)
    (hdenRoom : CompactComplexDenominatorCapacity.room scalarRows≤sh.chunk)
    (hledger : n≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows g.val).length)
    (hgrid : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        data i wire))
    (stack : Fin (tapes s roles)) (headerStack pcStack liveStack : Fin s)
    (ctrl : Fin 4 → Σ q,Program (tapes s roles) q 2)
    (classify : Fin (ctrl 0).1 → Bool)
    (i : Fin CompactComplexCompletedLiveLower.schedule.length)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=
      CompactComplexCompletedLiveLower.Event.scalar g) :
    let rawStage := CompactComplexNativeCodec.raw stage parentRows ell metadataP
    let nextStorage := storageOutput (liveProof (s:=s)) storage (n+(gates g).length)
    let nextPayload := emitted payload (fun j => CompactSpectatorLeafAxis.word
      (execute (block g) data (CompactComplexScalarRolePorts.roleIndex.symm j)))
    let nextCaller := bank control queue scalar rawStage tail nextStorage nextPayload
    ∃ m≤(CompactComplexScalarCountLifecycle.roleTimeConstant (block g)+1)*
        (parentRows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth),
      CompactComplexFixedNodePaths.nodePath (Nat.zero_lt_of_lt stack.isLt) stack
        (Actual.childReturn headerStack liveStack) ctrl (Actual.event headerStack pcStack liveStack) classify
        (CompactComplexScheduledPCLayout.eventPC i) (ready v) m
        (CompactComplexScheduledPCLayout.nextPC i) (ready (output v nextCaller)) := by
  dsimp only
  have h := group_step path stage parentRows hrows hG hK g ell p C axes metadataP n control queue scalar tail storage payload
    v hv data hw hblank hsource hlive ha hp haxes hroom hC baseline hbase hdenRoom hledger hgrid
  dsimp only at h
  have hr := h.1
  have he : (Actual.event headerStack pcStack liveStack (CompactComplexCompletedLiveLower.Event.scalar g))=
      Actual.scalar (s:=s) g := rfl
  rw [←he] at hr
  obtain ⟨m,hm,hpath⟩ := CompactComplexFixedNodePaths.scalar_path
    (Nat.zero_lt_of_lt stack.isLt) stack (Actual.childReturn headerStack liveStack) ctrl
    (Actual.event headerStack pcStack liveStack) classify i g hi _ _ _ hr
  have hparent : 0<parentRows := lt_of_lt_of_le hrows (Nat.div_le_self _ _)
  have hcount : 1≤(parentRows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2) := by
    have hpos : 0<parentRows*2^sh.bits*2^ell :=
      Nat.mul_pos (Nat.mul_pos hparent (pow_pos (by decide) _)) (pow_pos (by decide) _)
    have hW : 1≤ButterflyGuard.halfWidth metadataP sh.bits+2 := by omega
    have hC : 1≤parentRows*2^sh.bits*2^ell := by omega
    exact Nat.mul_le_mul hC hW
  have hV : 1≤parentRows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth :=
    hcount.trans (coefficient_volume sh parentRows ell metadataP)
  have hb := paid_join (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)) _ _
    (coefficient_volume sh parentRows ell metadataP) hV
  rw [←Nat.mul_assoc] at hb
  exact ⟨m,hm.trans hb,hpath⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarGeometryEventPath

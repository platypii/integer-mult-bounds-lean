import IntegerMultBounds.Machine.CompactComplexSourceReadyActualTable
import IntegerMultBounds.Machine.CompactComplexScalarGroupProgress

/-! Genuine original grouped scalar events on the full source-ready fixed
node table, retaining the next scalar-prefix grid and true live ledger. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventPath
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCallerEndpoint (storageOutput nativePayload)
open CompactComplexScalarNativeEndpoint (executed)
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

theorem group_step {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (parentRows : ℕ)
    (hrows : inp.rows=parentRows/roles) (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar
      (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head Actual.countHeader=0 ∧ storage.tape Actual.countHeader=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
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
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire)) :
    let stage := CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP
    let next := executed (block g) xs
    let nextStorage := storageOutput (liveProof (s:=s)) storage (n+(gates g).length)
    let nextPayload := nativePayload inp (block g) xs hw payload
    let nextCaller := bank control queue scalar stage tail nextStorage nextPayload
    HoareTime (Actual.scalar (s:=s) g).2
      (fun z => z=ready v) (fun z => z=ready (output v nextCaller))
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (parentRows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    (∀ a i j,(next a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (next a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1) ∧
    (∀ i wire,BoundedGrid (n+(gates g).length)
      (CompactFramedScalarGrid.bound (g.val+1)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (next a)) i wire)) ∧
    Live nextCaller (liveSlot (liveProof (s:=s))) (n+(gates g).length) ∧
    n+(gates g).length≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows (g.val+1)).length := by
  dsimp only
  have h := CompactComplexScalarGroupProgress.role_group_step (s:=10+s) path inp parentRows hrows
    (liveProof (s:=s)) Actual.countHeader Actual.countHeader_ne_live g ell p C axes metadataP n
    control queue scalar tail storage payload xs hw hblank hsource hlive ha hp haxes hroom hC
    baseline hbase hdenRoom hledger hgrid
  dsimp only at h
  obtain ⟨hr,hw',hg',hl',hb'⟩ := h
  rw [←hv] at hr
  have hr' := CompactComplexSourceReadyScalarWorkspace.role_realizes (s:=s)
    Actual.countHeader Actual.countHeader_ne_live (block g) v _ hr
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
    (inp : ActivePrefixStageFullData.Inputs sh) (parentRows : ℕ)
    (hrows : inp.rows=parentRows/roles) (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes (10+s) 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (v : Tapes (nodeTapes s roles) 2)
    (hv : permanent v=bank control queue scalar
      (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head Actual.countHeader=0 ∧ storage.tape Actual.countHeader=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
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
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire))
    (stack : Fin (tapes s roles)) (headerStack pcStack liveStack : Fin s)
    (ctrl : Fin 4 → Σ q,Program (tapes s roles) q 2)
    (classify : Fin (ctrl 0).1 → Bool)
    (i : Fin CompactComplexCompletedLiveLower.schedule.length)
    (hi : CompactComplexCompletedLiveLower.schedule.get i=
      CompactComplexCompletedLiveLower.Event.scalar g) :
    let stage := CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP
    let nextStorage := storageOutput (liveProof (s:=s)) storage (n+(gates g).length)
    let nextPayload := nativePayload inp (block g) xs hw payload
    let nextCaller := bank control queue scalar stage tail nextStorage nextPayload
    ∃ m≤(CompactComplexScalarCountLifecycle.roleTimeConstant (block g)+1)*
        (parentRows*(NativePolynomialStageShape.shape sh ell metadataP).recordWidth),
      CompactComplexFixedNodePaths.nodePath (Nat.zero_lt_of_lt stack.isLt) stack
        (Actual.childReturn headerStack liveStack) ctrl (Actual.event headerStack pcStack liveStack) classify
        (CompactComplexScheduledPCLayout.eventPC i) (ready v) m
        (CompactComplexScheduledPCLayout.nextPC i) (ready (output v nextCaller)) := by
  dsimp only
  have h := group_step path inp parentRows hrows g ell p C axes metadataP n control queue scalar tail storage payload
    v hv xs hw hblank hsource hlive ha hp haxes hroom hC baseline hbase hdenRoom hledger hgrid
  dsimp only at h
  have hr := h.1
  have he : (Actual.event headerStack pcStack liveStack (CompactComplexCompletedLiveLower.Event.scalar g))=
      Actual.scalar (s:=s) g := rfl
  rw [←he] at hr
  obtain ⟨m,hm,hpath⟩ := CompactComplexFixedNodePaths.scalar_path
    (Nat.zero_lt_of_lt stack.isLt) stack (Actual.childReturn headerStack liveStack) ctrl
    (Actual.event headerStack pcStack liveStack) classify i g hi _ _ _ hr
  have hparent : 0<parentRows := by
    have hh := inp.hr
    rw [hrows] at hh
    exact lt_of_lt_of_le hh (Nat.div_le_self _ _)
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
end IntegerMultBounds.Machine.CompactComplexSourceReadyScalarEventPath

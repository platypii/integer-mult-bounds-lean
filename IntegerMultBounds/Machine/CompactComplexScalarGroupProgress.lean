import IntegerMultBounds.Machine.CompactComplexScalarPrefixAdvance
import IntegerMultBounds.Machine.CompactComplexScalarCallerEndpoint
import IntegerMultBounds.Machine.CompactComplexRecursiveLiveProgress

/-! A genuine named scalar group returns the exact next native caller, the
next original scalar-prefix grid and the physically advanced live ledger.
Overflow uses the full node reserve; the induction postcondition retains the
strict prefix budget instead of replacing it by the coarse node allowance. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarGroupProgress
noncomputable section
open CompactComplexScalarIntegerRows (GroupIndex gates guardBits)
open CompactComplexScalarSegmentRows (block)
open CompactComplexScalarCountLifecycle (Realizes program)
open CompactComplexScalarCallerEndpoint (storageOutput nativePayload)
open CompactComplexScalarNativeEndpoint (executed)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarSequenceSemantics (values)
open CompactComplexScalarPathGuard (budget)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactComplexRecursiveLiveProgress (Live liveSlot)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open Networks.GaussianPrecision (BoundedGrid)
open ButterflyStreamData (Coefficient)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates
  Networks.ComplexFramedExecution.rows

private theorem flat_width {c N R w : ℕ} (xs : Fin c → Fin N → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) :
    ∀ a i,(ActivePrefixStageNativePolynomial.flattenArray (xs a) i).1.length=w ∧
      (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).2.length=w := by
  intro a i
  exact hw a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- All next-event native source premises, tighter numerical prefix bounds
and denominator ledger facts follow from this actual physical scalar group.
No child correctness or recursive execution claim is hidden in the step. -/
theorem group_step {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
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
    let stage := CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP
    let next := executed (block g) xs
    let nextStorage := storageOutput hs storage (n+(gates g).length)
    let nextPayload := nativePayload inp (block g) xs hw payload
    let nextCaller := bank control queue scalar stage tail nextStorage nextPayload
    Realizes (program hs header hh (block g))
      (bank control queue scalar stage tail storage payload) nextCaller
      (CompactComplexScalarCountLifecycle.timeConstant (block g)*
        (ActivePrefixStageTripleWords.count inp*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    (∀ a i j,(next a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (next a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1) ∧
    (∀ i wire,BoundedGrid (n+(gates g).length)
      (CompactFramedScalarGrid.bound (g.val+1)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (next a)) i wire)) ∧
    Live nextCaller (liveSlot hs) (n+(gates g).length) ∧
    n+(gates g).length≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows (g.val+1)).length := by
  dsimp only
  let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
  let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
  have hused : (CompactFramedScalarGrid.rows g.val).length≤scalarRows :=
    CompactComplexDenominatorCapacity.actual_prefix g.val
  have hcapacity := CompactComplexDenominatorCapacity.target_capacity path scalarRows baseline
    (metadataP-2*sh.bits) (CompactFramedScalarGrid.rows g.val).length n n (by omega)
    hused hdenRoom hledger (by omega)
  have hfield : n≤ButterflyGuard.halfWidth metadataP sh.bits+1 := by
    unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at hcapacity
    unfold ButterflyGuard.halfWidth
    omega
  have hrun := CompactComplexScalarCountLifecycle.runs_linear inp hs header hh (block g) ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    xs hw hblank hsource hlive hfield
  have hcaller := CompactComplexScalarCallerEndpoint.output_executed_bank inp hs header hh
    control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    (block g) xs hw n hblank
  dsimp only at hrun
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hrun
  have hgridOut := CompactComplexScalarPrefixAdvance.group_grid path g data p C axes metadataP n
    ha hp haxes hroom hC (flat_width xs hw) hgrid
  have hflat := CompactComplexScalarNativeEndpoint.executed_flat (block g) xs
  have hliveOut := CompactComplexRecursiveLiveProgress.scalar_output_live hs header hh v
    (CompactComplexScalarPolynomialSequence.execute (block g) data) (n+(block g).length)
  dsimp only [v,data] at hliveOut
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hliveOut
  have hledgerOut := CompactComplexRecursiveLiveProgress.scalar_segment_bound baseline levels frames returned
    (CompactFramedScalarGrid.rows g.val).length n (block g) hledger
  rw [←CompactComplexScalarSegmentRows.prefix_length,CompactComplexScalarSegmentRows.block_length] at hledgerOut
  refine ⟨by simpa only [Nat.add_assoc] using hrun,CompactComplexScalarNativeEndpoint.executed_width (block g) xs hw,?_,hliveOut,hledgerOut⟩
  intro i wire
  rw [hflat]
  exact hgridOut i wire

/-- Role-row execution retains the original node row descriptor. -/
theorem role_group_step {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (parentRows : ℕ)
    (hrows : inp.rows=parentRows/CompactComplexRolePhaseSite.roleCount) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (g : GroupIndex) (ell p C axes metadataP n : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
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
    let nextStorage := storageOutput hs storage (n+(gates g).length)
    let nextPayload := nativePayload inp (block g) xs hw payload
    let nextCaller := bank control queue scalar stage tail nextStorage nextPayload
    Realizes (CompactComplexScalarCountLifecycle.roleProgram hs header hh (block g))
      (bank control queue scalar stage tail storage payload) nextCaller
      (CompactComplexScalarCountLifecycle.roleTimeConstant (block g)*
        (parentRows*2^sh.bits*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    (∀ a i j,(next a i j).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (next a i j).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1) ∧
    (∀ i wire,BoundedGrid (n+(gates g).length)
      (CompactFramedScalarGrid.bound (g.val+1)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (next a)) i wire)) ∧
    Live nextCaller (liveSlot hs) (n+(gates g).length) ∧
    n+(gates g).length≤ledger scalarRows baseline levels frames returned
      (CompactFramedScalarGrid.rows (g.val+1)).length := by
  dsimp only
  let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload
  let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
  have hused : (CompactFramedScalarGrid.rows g.val).length≤scalarRows :=
    CompactComplexDenominatorCapacity.actual_prefix g.val
  have hcapacity := CompactComplexDenominatorCapacity.target_capacity path scalarRows baseline
    (metadataP-2*sh.bits) (CompactFramedScalarGrid.rows g.val).length n n (by omega)
    hused hdenRoom hledger (by omega)
  have hfield : n≤ButterflyGuard.halfWidth metadataP sh.bits+1 := by
    unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth at hcapacity
    unfold ButterflyGuard.halfWidth
    omega
  have hrun := CompactComplexScalarCountLifecycle.role_runs_linear inp parentRows hrows hs header hh (block g) ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    xs hw hblank hsource hlive hfield
  have hcaller := CompactComplexScalarCallerEndpoint.output_executed_bank inp hs header hh
    control queue scalar (CompactComplexNativeCodec.raw inp.stage parentRows ell metadataP) tail storage payload
    (block g) xs hw n hblank
  dsimp only at hrun
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hrun
  have hgridOut := CompactComplexScalarPrefixAdvance.group_grid path g data p C axes metadataP n
    ha hp haxes hroom hC (flat_width xs hw) hgrid
  have hflat := CompactComplexScalarNativeEndpoint.executed_flat (block g) xs
  have hliveOut := CompactComplexRecursiveLiveProgress.scalar_output_live hs header hh v
    (CompactComplexScalarPolynomialSequence.execute (block g) data) (n+(block g).length)
  dsimp only [v,data] at hliveOut
  rw [hcaller,CompactComplexScalarSegmentRows.block_length] at hliveOut
  have hledgerOut := CompactComplexRecursiveLiveProgress.scalar_segment_bound baseline levels frames returned
    (CompactFramedScalarGrid.rows g.val).length n (block g) hledger
  rw [←CompactComplexScalarSegmentRows.prefix_length,CompactComplexScalarSegmentRows.block_length] at hledgerOut
  refine ⟨by simpa only [Nat.add_assoc] using hrun,CompactComplexScalarNativeEndpoint.executed_width (block g) xs hw,?_,hliveOut,hledgerOut⟩
  intro i wire
  rw [hflat]
  exact hgridOut i wire

end
end IntegerMultBounds.Machine.CompactComplexScalarGroupProgress

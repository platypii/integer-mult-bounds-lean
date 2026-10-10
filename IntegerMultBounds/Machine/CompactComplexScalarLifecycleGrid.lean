import IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle
import IntegerMultBounds.Machine.CompactComplexScalarSequenceGrid

/-! Genuine original-header scalar lifecycles expose the numerical Gaussian
postcondition needed by recursive induction. The original dependency Path and
one retained field reserve derive every intermediate signed arithmetic guard. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarLifecycleGrid
noncomputable section
open CompactComplexScalarCountLifecycle (Realizes program output cost)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarIntegerRows (RowIndex guardBits)
open CompactComplexScalarSequenceSemantics (values circuit)
open CompactComplexScalarPathGuard (budget)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open Networks.GaussianPrecision (BoundedGrid)
open ButterflyStreamData (Coefficient)
open ButterflySigned (signedValue complexValue)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

private theorem flat_width {c N R w : ℕ} (xs : Fin c → Fin N → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) :
    ∀ a i,(ActivePrefixStageNativePolynomial.flattenArray (xs a) i).1.length=w ∧
      (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).2.length=w := by
  intro a i
  exact hw a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- Raw geometry physically supplies the count before scalar execution. The
actual returned words have the dependency-derived grid and true denominator;
no prepared count or per-row numerical guard is assumed. -/
theorem runs_from_path {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p C axes metadataP n : ℕ)
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
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤sh.chunk)
    (hgrid : ∀ a i,BoundedGrid n (budget p C levels frames returned axes)
      (complexValue (signedValue (ButterflyGuard.halfWidth metadataP sh.bits)
        (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).1)
        (signedValue (ButterflyGuard.halfWidth metadataP sh.bits)
        (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).2) n)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (n+ops.length))
      (cost ops (ActivePrefixStageTripleWords.count inp*2^ell)
        (ButterflyGuard.halfWidth metadataP sh.bits+1) n) ∧
    ∀ i wire,BoundedGrid (n+ops.length)
      (Networks.GaussianPrecision.scalarBound 1 52 (circuit ops)
        (budget p C levels frames returned axes))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (CompactComplexScalarPolynomialSequence.execute ops data) i wire) := by
  dsimp only
  have hrun := CompactComplexScalarCountLifecycle.runs inp hs header hh ops ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    xs hw hblank hsource hlive
  have hnumeric := CompactComplexScalarSequenceGrid.sequence_grid_from_path path ops
    (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) p C axes metadataP n
    ha hp haxes hroom (flat_width xs hw) hgrid
  exact ⟨hrun,hnumeric⟩

/-- Output fields retain their original physical widths independently of the
numerical reserve. The lifecycle places exactly these fields on role tapes. -/
theorem output_width {N : ℕ} (ops : List RowIndex)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    ∀ j i,(CompactComplexScalarPolynomialSequence.execute ops data j i).1.length=w ∧
      (CompactComplexScalarPolynomialSequence.execute ops data j i).2.length=w :=
  RawLinearCombinationComplexRowSequence.execute_width CompactComplexScalarRowBlock.wires_pos
    CompactComplexScalarPolynomialSequence.rows ops data w hw

/-- The same dependency-derived grid accompanies the uniformly paid physical
lifecycle once its live denominator has retained-field capacity. -/
theorem runs_linear_from_path {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p C axes metadataP n : ℕ)
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
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤sh.chunk)
    (hcapacity : n≤ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ a i,BoundedGrid n (budget p C levels frames returned axes)
      (complexValue (signedValue (ButterflyGuard.halfWidth metadataP sh.bits)
        (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).1)
        (signedValue (ButterflyGuard.halfWidth metadataP sh.bits)
        (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).2) n)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (n+ops.length))
      (CompactComplexScalarCountLifecycle.timeConstant ops*
        (ActivePrefixStageTripleWords.count inp*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    ∀ i wire,BoundedGrid (n+ops.length)
      (Networks.GaussianPrecision.scalarBound 1 52 (circuit ops)
        (budget p C levels frames returned axes))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (CompactComplexScalarPolynomialSequence.execute ops data) i wire) := by
  dsimp only
  have hrun := CompactComplexScalarCountLifecycle.runs_linear inp hs header hh ops ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    xs hw hblank hsource hlive hcapacity
  have hnumeric := CompactComplexScalarSequenceGrid.sequence_grid_from_path path ops
    (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) p C axes metadataP n
    ha hp haxes hroom (flat_width xs hw) hgrid
  exact ⟨hrun,hnumeric⟩

/-- Genuine contiguous scalar prefixes use the complete node allowance once.
The physical block and original-header cleanup accompany the preserved Path
budget, rather than charging a new scalar-growth factor at each segment. -/
theorem runs_prefix_linear_from_path {sh : CompactGadgetReservationShape.Shape}
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p C axes metadataP n : ℕ)
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
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤sh.chunk)
    (hcapacity : n≤ButterflyGuard.halfWidth metadataP sh.bits+1)
    (before after : List (Networks.Circuit.Gate CompactComplexScalarIntegerRows.Wire ℂ))
    (hsegment : before++circuit ops++after=
      Networks.RationalScalarGrid.castRows Networks.ComplexFramedExecution.rows)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hgrid : ∀ wire i,BoundedGrid n
      (Networks.GaussianPrecision.scalarBound 1 52 before
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell metadataP) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (n+ops.length))
      (CompactComplexScalarCountLifecycle.timeConstant ops*
        (ActivePrefixStageTripleWords.count inp*2^ell)*(ButterflyGuard.halfWidth metadataP sh.bits+2)) ∧
    ∀ i wire,BoundedGrid (n+ops.length)
      (budget p C levels frames returned axes)
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (CompactComplexScalarPolynomialSequence.execute ops data) i wire) := by
  dsimp only
  have hrun := CompactComplexScalarCountLifecycle.runs_linear inp hs header hh ops ell metadataP
    (ButterflyGuard.halfWidth metadataP sh.bits+1) n control queue scalar tail storage payload
    xs hw hblank hsource hlive hcapacity
  have hnumeric := CompactComplexScalarSequenceGrid.sequence_prefix_grid_from_path path ops
    (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) p C axes metadataP n
    ha hp haxes hroom before after hsegment hC (flat_width xs hw) hgrid
  exact ⟨hrun,hnumeric⟩

end
end IntegerMultBounds.Machine.CompactComplexScalarLifecycleGrid

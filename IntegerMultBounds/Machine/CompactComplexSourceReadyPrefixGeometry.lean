import IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixReadiness

/-! Executed scalar polynomial rows are the genuine row-major arrays used by
the next child entry. Cardinality casts retain literal native words, coefficient
widths and the exact scalar-prefix grid; no physical execution is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixGeometry
noncomputable section
open ButterflyStreamData (Coefficient)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (RowIndex wireIndex)
open CompactComplexScalarNativeEndpoint (executed executed_width)
open CompactComplexScalarSequenceSemantics (values)
open CompactComplexSourceReadyPrefixReadiness (fullPort)
open CompactComplexSpectatorTargetBank (roleSlot)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexScalarCallerEndpoint (storageOutput nativePayload)
open CompactComplexScalarRolePorts (roleIndex)
open CompactComplexRolePhaseSite (roleCount)
open Networks.GaussianPrecision (BoundedGrid)
variable {sh : CompactGadgetReservationShape.Shape}

theorem cardinality (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows) :
    ActivePrefixStageTripleWords.count inp*2^ell=
      ButterflySpectatorGeometry.Size rows sh.bits (2^ell) := by
  rw [←CompactComplexScalarCountHeaders.native_count inp ell,hrows]
  unfold ButterflySpectatorGeometry.Size
  exact Nat.mul_assoc _ _ _

/-- The canonical cast preserves the original flattened coefficient order. -/
def array (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient) :
    CompactSpectatorVisitGeometry.Array sh rows ell :=
  fun i => ActivePrefixStageNativePolynomial.flattenArray xs
    (Fin.cast (cardinality inp rows ell hrows).symm i)

theorem array_at (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (i : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell))) :
    array inp rows ell hrows xs i=ActivePrefixStageNativePolynomial.flattenArray xs
      (Fin.cast (cardinality inp rows ell hrows).symm i) := rfl

private theorem word_cast {N M : ℕ} (he : N=M) (f : Fin N → Coefficient) :
    NativeZeroPaddingArray.word (fun i : Fin M => f (Fin.cast he.symm i))=
      NativeZeroPaddingArray.word f := by
  unfold NativeZeroPaddingArray.word
  exact (congrArg List.flatten (List.ofFn_congr he (fun i => ButterflyStreamData.encoded (f i)))).symm

/-- The child-entry array word is exactly the actual native scalar stream. -/
theorem array_word (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    NativeZeroPadding.word (NativeZeroPaddingArray.word (array inp rows ell hrows xs))=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp xs hw))) := by
  rw [CompactComplexSourceReadyPrefixReadiness.native_array_word]
  exact congrArg NativeZeroPadding.word (word_cast (cardinality inp rows ell hrows) _)

theorem array_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell w : ℕ)
    (hrows : inp.rows=rows)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ∀ i,(array inp rows ell hrows xs i).1.length=w ∧
      (array inp rows ell hrows xs i).2.length=w := by
  intro i
  exact hw _ _

theorem retained_half (p : ℕ) (hp : 2*sh.bits ≤ p) :
    CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)=ButterflyGuard.halfWidth p sh.bits := by
  unfold CompactSpectatorInheritedGrid.half ButterflyGuard.halfWidth
  omega

/-- Exact retained native widths supply the descendant butterfly Width. -/
theorem array_inherited_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs i j).2.length=ButterflyGuard.halfWidth p sh.bits+1) :
    CompactSpectatorInheritedGrid.Width sh rows ell (p-2*sh.bits)
      (array inp rows ell hrows xs) := by
  apply CompactSpectatorInheritedGrid.width_from_retained_role sh rows ell p hp
  exact array_width inp rows ell _ hrows xs hw

/-- Child-array decoding and the scalar circuit's named-wire decoding are
literally identical after the canonical cardinality cast. -/
theorem array_decode (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n : ℕ)
    (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (a : Fin wireCount) (i : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell))) :
    CompactSpectatorInheritedGrid.decoded sh rows ell (p-2*sh.bits) n
      (array inp rows ell hrows (xs a)) i=
    values (ButterflyGuard.halfWidth p sh.bits) n
      (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a))
      (Fin.cast (cardinality inp rows ell hrows).symm i) (wireIndex.symm a) := by
  unfold CompactSpectatorInheritedGrid.decoded values ButterflyStreamSemantics.decode
  rw [retained_half p hp]
  simp only [Equiv.apply_symm_apply]
  rfl

theorem array_grid (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n M : ℕ)
    (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hg : ∀ i wire,BoundedGrid n M
      (values (ButterflyGuard.halfWidth p sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) i wire)) (a : Fin wireCount) :
    CompactSpectatorInheritedGrid.Grid sh rows ell (p-2*sh.bits) n M
      (array inp rows ell hrows (xs a)) := by
  intro i
  rw [array_decode inp rows ell p n hrows hp xs a i]
  exact hg _ _

/-- The actual executed named array, reindexed only by retained geometry. -/
def nextArray (inp : ActivePrefixStageFullData.Inputs sh) (rows ell : ℕ)
    (hrows : inp.rows=rows) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (a : Fin wireCount) : CompactSpectatorVisitGeometry.Array sh rows ell :=
  array inp rows ell hrows (executed ops xs a)

theorem nextArray_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1) (a : Fin wireCount) :
    CompactSpectatorInheritedGrid.Width sh rows ell (p-2*sh.bits)
      (nextArray inp rows ell hrows ops xs a) :=
  array_inherited_width inp rows ell p hrows hp _ (executed_width ops xs hw a)

/-- Literal record widths required by physical child entry, before switching
to the descendant's inherited-precision presentation. -/
theorem nextArray_retained_width (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p : ℕ)
    (hrows : inp.rows=rows) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1) (a : Fin wireCount) :
    ∀ i,(nextArray inp rows ell hrows ops xs a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (nextArray inp rows ell hrows ops xs a i).2.length=CompactNativeRoleHeaders.recordWidth sh p :=
  array_width inp rows ell _ hrows _ (executed_width ops xs hw a)

theorem nextArray_grid (inp : ActivePrefixStageFullData.Inputs sh) (rows ell p n M : ℕ)
    (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p) (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hg : ∀ i wire,BoundedGrid n M
      (values (ButterflyGuard.halfWidth p sh.bits) n
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (executed ops xs a)) i wire))
    (a : Fin wireCount) :
    CompactSpectatorInheritedGrid.Grid sh rows ell (p-2*sh.bits) n M
      (nextArray inp rows ell hrows ops xs a) :=
  array_grid inp rows ell p n M hrows hp (executed ops xs) hg a

/-- Actual selected role tape after a scalar event is already the literal
child-entry Array word, with cardinality and serialization derived internally. -/
theorem full_next_array {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh)
    (rows ell w d : ℕ) (hrows : inp.rows=rows) (hs : 7<10+s)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roleCount) 2)
    (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s roleCount) 2)
    (a : Fin wireCount) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    endpoint.head (fullPort (roleSlot (roleIndex a)))=0 ∧
    endpoint.tape (fullPort (roleSlot (roleIndex a)))=
      NativeZeroPadding.word (NativeZeroPaddingArray.word (nextArray inp rows ell hrows ops xs a)) := by
  dsimp only
  have hr := CompactComplexSourceReadyPrefixReadiness.full_next_role inp hs control queue scalar stage tail
    storage payload ops xs hw d v a
  have he := array_word inp rows ell w hrows (executed ops xs a) (executed_width ops xs hw a)
  exact ⟨hr.1,hr.2.trans he.symm⟩

/-- Complete selected-role readiness from the actual scalar endpoint: its
physical word, retained widths and inherited grid all describe the same array. -/
theorem full_next_array_ready {s : ℕ} (inp : ActivePrefixStageFullData.Inputs sh)
    (rows ell p d M : ℕ) (hrows : inp.rows=rows) (hp : 2*sh.bits ≤ p) (hs : 7<10+s)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+roleCount) 2)
    (ops : List RowIndex)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=ButterflyGuard.halfWidth p sh.bits+1 ∧
      (xs a i j).2.length=ButterflyGuard.halfWidth p sh.bits+1)
    (hg : ∀ i wire,BoundedGrid d M
      (values (ButterflyGuard.halfWidth p sh.bits) d
        (fun a => ActivePrefixStageNativePolynomial.flattenArray (executed ops xs a)) i wire))
    (v : Tapes (CompactComplexSourceReadyScalarWorkspace.nodeTapes s roleCount) 2)
    (a : Fin wireCount) :
    let next := bank control queue scalar stage tail (storageOutput hs storage d)
      (nativePayload inp ops xs hw payload)
    let endpoint := CompactComplexSourceReadyScalarWorkspace.ready
      (CompactComplexSourceReadyScalarWorkspace.output v next)
    let f := nextArray inp rows ell hrows ops xs a
    (endpoint.head (fullPort (roleSlot (roleIndex a)))=0 ∧
      endpoint.tape (fullPort (roleSlot (roleIndex a)))=
        NativeZeroPadding.word (NativeZeroPaddingArray.word f)) ∧
    CompactSpectatorInheritedGrid.Width sh rows ell (p-2*sh.bits) f ∧
    CompactSpectatorInheritedGrid.Grid sh rows ell (p-2*sh.bits) d M f := by
  exact ⟨full_next_array inp rows ell _ d hrows hs control queue scalar stage tail
    storage payload ops xs hw v a,
    nextArray_width inp rows ell p hrows hp ops xs hw a,
    nextArray_grid inp rows ell p d M hrows hp ops xs hg a⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixGeometry

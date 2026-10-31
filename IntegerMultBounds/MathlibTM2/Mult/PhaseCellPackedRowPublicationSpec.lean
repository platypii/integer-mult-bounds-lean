module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile

/-! Index the actual packed row certificates in publication order. This works
for arbitrary core subsets: seam rows can be supplied by the separate full-line
fallback, without pretending that every generated halo is a proper interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {A s t B L : ℕ} [NeZero s] [NeZero t] {batch : PackedExactBatch A s t B L}

/-- The returned row at replica `j` has the same unit-ball and exact-inverse
certificate as its actual input field. -/
theorem Rows.replica_spec (rows : batch.Rows) (i : Fin batch.records.length)
    (F : Fin B → ZMod s → GaussianInt) (hF : (batch.records.get i).Fs = List.ofFn F) (j : Fin B) :
    let r := batch.records.get i
    let out := packedIntervalRead r.p r.W (coreStart r.coreWidth r.k) (cstream A r.W (rows.values i j))
    (∀ z ∈ ownedCore s r.coreWidth r.k, ‖out z‖ ≤ 1) ∧
    ErrorOn (ownedCore s r.coreWidth r.k) out
      ((((2 : ℂ)^inverseNormalizationShift r.p)⁻¹ • batch.J r) ((1/2 : ℂ) • fun z => value r.p (F j z)))
      (3/(2 : ℝ)^r.p) := by
  have h := (rows.exactOutput i).2.2
  rw [hF] at h
  have hj := h.get (i := j.val) (by simp only [List.length_ofFn]; exact j.isLt)
    (by simp only [List.length_ofFn]; exact j.isLt)
  simpa only [List.get_eq_getElem,List.getElem_ofFn] using hj

/-- Common job metadata turns local solver certificates into the uniform
reader/target/error language used by publication. No output accuracy is assumed. -/
theorem Rows.publication_spec (rows : batch.Rows) (p width : ℕ)
    (ks : Fin batch.records.length → ℕ) (F : Fin B → ZMod s → GaussianInt)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ r ∈ batch.records, r.p = p)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width)
    (hk : ∀ i : Fin batch.records.length, (batch.records.get i).k = ks i)
    (hF : ∀ r ∈ batch.records, r.Fs = List.ofFn F)
    (hJ : ∀ r ∈ batch.records, batch.J r = J) :
    ∀ i j,
      let out := packedIntervalRead p batch.W (coreStart width (ks i)) (cstream A batch.W (rows.values i j))
      (∀ z ∈ ownedCore s width (ks i), ‖out z‖ ≤ 1) ∧
      ErrorOn (ownedCore s width (ks i)) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (F j z)))
        (3/(2 : ℝ)^p) := by
  intro i j
  have hi : batch.records.get i ∈ batch.records := List.get_mem _ _
  have h := rows.replica_spec i F (hF _ hi) j
  simpa only [hp _ hi,batch.hwidth _ hi,hwidth _ hi,hk i,hJ _ hi] using h

/-- Actual transpose padding preserves each indexed numerical certificate at
its returned real-row position. Padding bytes require no numerical hypothesis. -/
theorem Rows.padded_publication_spec (rows : batch.Rows)
    (tile : ArchiveTilePlan.Result L rows.values) (p width : ℕ)
    (ks : Fin batch.records.length → ℕ) (F : Fin B → ZMod s → GaussianInt)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ r ∈ batch.records, r.p = p)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width)
    (hk : ∀ i : Fin batch.records.length, (batch.records.get i).k = ks i)
    (hF : ∀ r ∈ batch.records, r.Fs = List.ofFn F)
    (hJ : ∀ r ∈ batch.records, batch.J r = J) :
    ∀ i j,
      let out := packedIntervalRead p batch.W (coreStart width (ks i))
        (cstream A batch.W (tile.padded (paddedCoreIndex tile.capacity_ge i) j))
      (∀ z ∈ ownedCore s width (ks i), ‖out z‖ ≤ 1) ∧
      ErrorOn (ownedCore s width (ks i)) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (F j z)))
        (3/(2 : ℝ)^p) := by
  simpa only [tile.realRows] using rows.publication_spec p width ks F J hp hwidth hk hF hJ

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch

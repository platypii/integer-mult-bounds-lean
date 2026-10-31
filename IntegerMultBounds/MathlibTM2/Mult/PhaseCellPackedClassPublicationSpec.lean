module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRowPublicationSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIndexedCoreTileRows

/-! Actual packed output supplies a publication class from its job-key order.
All row lengths, accuracy and unit-ball claims are derived; callers supply
only equality of ordinary job metadata with the selected class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {A s t B L width : ℕ} [NeZero s] [NeZero t] {batch : PackedExactBatch A s t B L}

theorem class_key_count (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) : g.indices.length = batch.records.length := by
  simpa only [List.length_map] using (congrArg List.length hkeys).symm

theorem class_key_get (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) (i : Fin batch.records.length) :
    (batch.records.get i).k = g.indices[i.val]'(by rw [class_key_count g hkeys]; exact i.isLt) := by
  have hg : i.val < g.indices.length := by rw [class_key_count g hkeys]; exact i.isLt
  have he := congrArg (fun xs : List ℕ => xs[i.val]?) hkeys
  simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem hg,Option.map_some,
    Option.some.injEq] at he
  exact he

def Rows.classRows (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) : Fin B → ℕ → List GaussianInt :=
  indexedCoreRows g.indices (class_key_count g hkeys) rows.values

theorem Rows.classRows_map (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) (j : Fin B) :
    g.indices.map (rows.classRows g hkeys j) = List.ofFn (fun i => rows.values i j) :=
  indexedCoreRows_map g.indices (class_key_count g hkeys) g.indices_nodup rows.values j

theorem Rows.classRows_length (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width) :
    ∀ j k, k ∈ g.indices → (rows.classRows g hkeys j k).length = g.length := by
  intro j
  apply indexedCoreRows_forall g.indices (class_key_count g hkeys) g.indices_nodup rows.values j
    (fun _ row => row.length = g.length)
  intro i
  have hi : batch.records.get i ∈ batch.records := List.get_mem _ _
  have hlen := batch.hcore _ hi
  rw [hwidth _ hi,class_key_get g hkeys i] at hlen
  have hk := (mem_corePublicationIndices s width g.length _).mp
    (g.sublist.subset (List.getElem_mem (show i.val < g.indices.length by rw [class_key_count g hkeys]; exact i.isLt)))
  exact (rows.length i j).trans (hlen.symm.trans hk.2)

/-- The class-major scheduler's numerical premise follows from the exact
producer certificate, without any assumption about computed output rows. -/
theorem Rows.classRows_spec (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (p : ℕ) (F : Fin B → ZMod s → GaussianInt)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hp : ∀ r ∈ batch.records, r.p = p) (hwidth : ∀ r ∈ batch.records, r.coreWidth = width)
    (hF : ∀ r ∈ batch.records, r.Fs = List.ofFn F) (hJ : ∀ r ∈ batch.records, batch.J r = J) :
    ∀ j k, k ∈ g.indices →
      let out := packedIntervalRead p batch.W (coreStart width k) (cstream A batch.W (rows.classRows g hkeys j k))
      (∀ z ∈ ownedCore s width k, ‖out z‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (F j z)))
        (3/(2 : ℝ)^p) := by
  have hspec := rows.publication_spec p width
    (fun i => g.indices[i.val]'(by rw [class_key_count g hkeys]; exact i.isLt)) F J hp hwidth
    (class_key_get g hkeys) hF hJ
  intro j
  exact indexedCoreRows_forall g.indices (class_key_count g hkeys) g.indices_nodup rows.values j
    (fun k row =>
      let out := packedIntervalRead p batch.W (coreStart width k) (cstream A batch.W row)
      (∀ z ∈ ownedCore s width k, ‖out z‖ ≤ 1) ∧
      ErrorOn (ownedCore s width k) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun z => value p (F j z)))
        (3/(2 : ℝ)^p)) (fun i => hspec i j)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch

module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! Packed jobs already return cropped cores. Their coefficient-row interface
therefore needs no ambient scan, crop executor or extra rounding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

noncomputable def rowTarget (r : PackedNormalizedJob A s) (F : ZMod s → GaussianInt) (i : ZMod s) : ℂ :=
  ((2 : ℂ)^inverseNormalizationShift r.p)⁻¹*componentSolution r.Y F i

noncomputable def rowError (r : PackedNormalizedJob A s) : ℝ :=
  (2/(2 : ℝ)^r.p+(1/(2 : ℝ)^r.targetOut)/(2 : ℝ)^inverseNormalizationShift r.p)+
    (1/(2 : ℝ)^r.localityTarget+1/(2 : ℝ)^r.localityTarget)/(2 : ℝ)^inverseNormalizationShift r.p

def RowOutput (r : PackedNormalizedJob A s) (rows : List (List GaussianInt)) : Prop :=
  rows.length = r.Fs.length ∧
    (∀ row ∈ rows, row.length = coreLength s r.coreWidth r.k) ∧
    List.Forall₂ (fun F row => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k) (cstream A r.W row))
      (r.rowTarget F) r.rowError) r.Fs rows

theorem output_rows {r : PackedNormalizedJob A s} {word : List (Fin (A+4))}
    (h : r.output word) :
    ∃ rows : List (List GaussianInt), word = cstream A r.W rows.flatten ∧ r.RowOutput rows := by
  obtain ⟨Gs,hcount,hword,hgood⟩ := h
  let rows := Gs.map (ownedCoreWords r.coreWidth r.k)
  have hbytes : cstream A r.W rows.flatten =
      (Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten := by
    simpa only [List.flatMap] using cstream_flatMap_rows (A := A) (w := r.W) Gs (ownedCoreWords r.coreWidth r.k)
  refine ⟨rows,hword.trans hbytes.symm,by simpa only [rows,List.length_map] using hcount,?_,?_⟩
  · intro row hr
    obtain ⟨D,hD,he⟩ := List.mem_map.mp hr
    subst row
    exact ownedCoreWords_length r.coreWidth r.k D
  · apply List.forall₂_map_right_iff.mpr
    exact hgood

theorem outputs_rows (W : ℕ) {records : List (PackedNormalizedJob A s)}
    {outputs : List (List (Fin (A+4)))}
    (hwidth : ∀ r ∈ records, r.W = W) (h : List.Forall₂ PackedNormalizedJob.output records outputs) :
    ∃ rowBatches : List (List (List GaussianInt)),
      outputs = rowBatches.map (fun rows => cstream A W rows.flatten) ∧ List.Forall₂ RowOutput records rowBatches := by
  induction h with
  | nil => exact ⟨[],rfl,.nil⟩
  | @cons r word records outputs hhead htail ih =>
    obtain ⟨rows,hword,hr⟩ := output_rows hhead
    obtain ⟨rowBatches,ht,hrows⟩ := ih (fun r hr => hwidth r (by simp [hr]))
    refine ⟨rows::rowBatches,?_,.cons hr hrows⟩
    rw [hword,hwidth r (by simp),ht]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob

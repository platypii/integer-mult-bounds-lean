module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJob

/-! Expose the physical recovery certificate as ordinary fitted scalar fields.
The reverse replica order is explicit so complex assembly can consume it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

/-- Recovery returns fitted scalar fields in reverse replica order, with the
numerical certificate attached to precisely the fields encoded on the tape. -/
theorem GeneratedRecoveryOutput.fields {H : ReplicaHaloProblem s} {target : ℕ}
    {X : ℕ → ZMod s → ℝ} {word : List (Fin (A+4))}
    (h : GeneratedRecoveryOutput H target X word) :
    ∃ E : Fin H.Fs.length → ZMod s → GaussianInt,
      word = ((List.finRange H.Fs.length).reverse.map
        (fun r => cstream A H.wordWidth (packedInterval H.origin H.span (E r)))).flatten ∧
      ∀ r, (∀ i, Fits H.wordWidth (E r i)) ∧
        PhaseCellInterface.ErrorOn (PhaseCellDiscreteGeometry.haloVertices s H.origin (H.origin+H.span))
          (fun i => (value H.precision (E r i)).re) (X r.val) (1/(2 : ℝ)^target) := by
  obtain ⟨B,Ds,outputs,_,hcert,hword⟩ := h
  let E := fun r : Fin H.Fs.length => B.recoveredField r (Ds.getD r.val (fun _ => 0))
  have hparts := hcert.imp (fun r words hr =>
    show ((∀ i, Fits H.wordWidth (E r i)) ∧
      PhaseCellInterface.ErrorOn (PhaseCellDiscreteGeometry.haloVertices s H.origin (H.origin+H.span))
        (fun i => (value H.precision (E r i)).re) (X r.val) (1/(2 : ℝ)^target)) ∧
      words = cstream A H.wordWidth (packedInterval H.origin H.span (E r)) from ⟨hr.2,hr.1⟩)
  obtain ⟨hgood,hstreams⟩ := (List.forall₂_and_left _ _).mp hparts
  have heq : outputs = (List.finRange H.Fs.length).map
      (fun r => cstream A H.wordWidth (packedInterval H.origin H.span (E r))) := by
    clear hparts hcert hword
    generalize List.finRange H.Fs.length = indices at hstreams ⊢
    induction hstreams with
    | nil => rfl
    | cons hx hs ih => simp only [List.map_cons,hx,ih]
  refine ⟨E,?_,fun r => hgood r (List.mem_finRange r)⟩
  rw [hword,heq,← List.map_reverse]

/-- The scalar error holds for reads of the fitted encoded fields, with any
following tape suffix. No separate decoded-output witness is required. -/
theorem RawRecoveryJob.output_fields_read (r : RawRecoveryJob s) (hA : 4 ≤ A)
    {word : List (Fin (A+4))} (h : r.output word) (tail : List (Fin (A+4))) :
    ∃ E : Fin r.problem.Fs.length → ZMod s → GaussianInt,
      word = ((List.finRange r.problem.Fs.length).reverse.map
        (fun j => cstream A r.problem.wordWidth
          (packedInterval r.problem.origin r.problem.span (E j)))).flatten ∧
      ∀ j, (∀ i, Fits r.problem.wordWidth (E j i)) ∧
        PhaseCellInterface.ErrorOn
          (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
          (fun i => (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
            (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span (E j))++tail) i).re)
          (r.solution j.val) (1/(2 : ℝ)^r.target) := by
  obtain ⟨E,hword,hgood⟩ := GeneratedRecoveryOutput.fields h
  refine ⟨E,hword,fun j => ⟨(hgood j).1,?_⟩⟩
  intro i hi
  obtain ⟨ha,hb⟩ := (PhaseCellDiscreteGeometry.mem_haloVertices _ _ i).mp hi
  have hw : 0 < r.problem.wordWidth := by
    unfold ReplicaHaloProblem.wordWidth executionWidth
    omega
  dsimp only
  rw [packedIntervalRead_eq r.problem.precision r.problem.wordWidth r.problem.origin
    r.problem.span (E j) tail [] r.problem.span_fit i ha hb,
    pairedCellRead_encodedField hA hw (E j) [] i ((hgood j).1 i)]
  exact (hgood j).2 i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryDescriptorStep

/-! Mathematical jobs for the fixed cached physical recovery machine.
Job data contain no executions, supplied factors or register-readiness premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure GeneratedRecoveryJob (s : ℕ) [NeZero s] where
  problem : ReplicaHaloProblem s
  target : ℕ
  solution : ℕ → ZMod s → ℝ
  span_fit : problem.span+problem.band ≤ s
  origin_lt : problem.origin < s
  precision_ge : 2 ≤ problem.p
  width_fit : 8*problem.p ≤ 2^problem.u
  padding : 2*((s/(problem.t-s)+1)-2*problem.band) ≤ 2^problem.l+1
  solves : ∀ r < problem.Fs.length,
    Solves (realMatrix s problem.t problem.p problem.u) (haloVertices s problem.origin (problem.origin+problem.span))
      (solution r) (fun i => (value problem.precision (problem.Fs.reverse.getD r (fun _ => 0) i)).re)
  sizing : problem.target = boundaryHaloTarget problem.p problem.u (boundaryRecoveryTarget problem.p target) problem.rhsExp
    (haloBoundary s problem.t problem.band problem.origin (problem.origin+problem.span)).card

namespace GeneratedRecoveryJob
variable {s A : ℕ} [NeZero s]

noncomputable def words (r : GeneratedRecoveryJob s) : Fin 392 → List (Fin (A+4)) :=
  (generatedRecoveryInput r.problem [] []).R

def output (r : GeneratedRecoveryJob s) (word : List (Fin (A+4))) : Prop :=
  GeneratedRecoveryOutput r.problem r.target r.solution word

def outputVolume (r : GeneratedRecoveryJob s) : ℕ := r.problem.Fs.length*(r.problem.span*r.problem.wordWidth)

theorem output_length (r : GeneratedRecoveryJob s) {word : List (Fin (A+4))} (h : r.output word) :
    word.length = r.outputVolume := by
  obtain ⟨B,Ds,outputs,_,hcert,hword⟩ := h
  have hlength (indices : List (Fin r.problem.Fs.length)) (ys : List (List (Fin (A+4))))
      (h : List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) indices ys) :
      ys.flatten.length = indices.length*(r.problem.span*r.problem.wordWidth) := by
    induction h with
    | nil => simp
    | cons hx hs ih =>
      simp only [List.flatten_cons,List.length_append,List.length_cons]
      rw [hx.1,length_cstream,packedInterval_length _ r.problem.span_fit]
      rw [ih]
      ring
  have hsum := hlength _ _ hcert
  rw [hword]
  simpa only [outputVolume,List.length_flatten,List.map_reverse,List.sum_reverse,List.length_finRange] using hsum

theorem outputs_length {records : List (GeneratedRecoveryJob s)} {outputs : List (List (Fin (A+4)))}
    (h : List.Forall₂ output records outputs) : outputs.flatten.length = (records.map outputVolume).sum := by
  induction h with
  | nil => simp
  | @cons r word records outputs hr hs ih =>
    simp only [List.flatten_cons,List.length_append,List.map_cons,List.sum_cons]
    rw [r.output_length hr,ih]

end GeneratedRecoveryJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

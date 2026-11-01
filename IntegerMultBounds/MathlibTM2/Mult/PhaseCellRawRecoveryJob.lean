module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryJob
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedRecoveryDescriptorStep

/-! Raw recovery jobs extend mathematical halo jobs with ordinary input words
and their exact normalization relation. No executions or resource bounds are stored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure RawRecoveryJob (s : ℕ) [NeZero s] extends GeneratedRecoveryJob s where
  inputFields : List (ZMod s → GaussianInt)
  W : ℕ
  fields : problem.Fs = recoveryInputFields problem.p problem.precision inputFields
  precision_fit : problem.p+1 ≤ problem.precision
  format_fit : problem.wordWidth ≤ W

namespace RawRecoveryJob
variable {s Q A : ℕ} [NeZero s] {U : Type}

noncomputable def words (r : RawRecoveryJob s) : Fin 392 → List (Fin (A+4)) :=
  (rawRecoveryInput r.problem r.W r.inputFields [] []).R

def output (r : RawRecoveryJob s) (word : List (Fin (A+4))) : Prop :=
  r.toGeneratedRecoveryJob.output word

def outputVolume (r : RawRecoveryJob s) : ℕ := r.toGeneratedRecoveryJob.outputVolume

def inputTime (r : RawRecoveryJob s) : ℕ := normalizeRecoveryInputCost r.problem r.W r.inputFields.length

noncomputable def initialStock (r : RawRecoveryJob s) : ℕ :=
  registerBankStock (rawRecoveryInput (A := A) r.problem r.W r.inputFields [] [])

noncomputable def runTime (r : RawRecoveryJob s) (B : ReplicaRecoveryBatch r.problem r.target r.solution) : ℕ :=
  r.inputTime+generatedReplicaBoundaryFactoryCost r.problem r.target+
    firstCachedReplicaRecoveryTime r.problem (B.problem r.sizing)

noncomputable def runStock (r : RawRecoveryJob s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K : ℕ)
    (B : ReplicaRecoveryBatch r.problem r.target r.solution) : ℕ :=
  r.initialStock (A := A)+
    (normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*r.inputTime+generatedRecoveryInputStock r.problem [] []+
      generatedFirstCachedReplicaRecoveryWorkspace r.problem (B.problem r.sizing) r.target hR hQ push c M R K)

theorem outputs_length {records : List (RawRecoveryJob s)} {outputs : List (List (Fin (A+4)))}
    (h : List.Forall₂ output records outputs) : outputs.flatten.length = (records.map outputVolume).sum := by
  induction h with
  | nil => simp
  | @cons r word records outputs hr hs ih =>
    simp only [List.flatten_cons,List.length_append,List.map_cons,List.sum_cons]
    rw [r.toGeneratedRecoveryJob.output_length hr,ih]
    rfl

end RawRecoveryJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

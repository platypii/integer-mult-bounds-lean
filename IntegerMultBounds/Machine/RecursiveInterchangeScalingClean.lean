import IntegerMultBounds.Machine.RecursiveInterchangeScalingConstruct
import IntegerMultBounds.Machine.FlatCoordinateScalingSharedBank
import IntegerMultBounds.Machine.CleanExecution

/-! Reusable initialized heterogeneous scalings: retain six original headers and
the normalized payload pair, physically erase every private tape and tracker. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeScalingClean
open Networks
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Target)
open Shared50ModularControl (prime)
open RecursiveInterchangeScalingConstruct (TapeCount sourceSlot destSlot headerSlot)
noncomputable section

def right (r : ℚ) (i : Fin (TapeCount r)) : Bool := decide (3 ≤ i.val ∧ i.val < 9)
def keep (r : ℚ) (i : Fin (TapeCount r)) : Bool := right r i || decide (i = sourceSlot r ∨ i = destSlot r)

def bank {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :=
  (RecursiveInterchangeScalingConstruct.input (r := r) hs a t).append (SharedBank.empty (TapeCount r) prime)

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (t : Target) :=
  CleanExecution.program (RecursiveInterchangeScalingConstruct.program hr t) (right r) (keep r)

def bound (r : ℚ) (V : ℕ) : ℕ :=
  (2+5*TapeCount r)*((2428+120*(r.num.natAbs+r.den)+22*RecursiveScalingInstall.LocalTapes r.num.natAbs r.den)*V+401)+
    11*TapeCount r+4

/-- The reusable physical bank is independent of which coordinate is scaled. -/
theorem bank_target {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t u : Target) :
    bank (r := r) hs a t = bank (r := r) hs a u := by
  unfold bank
  rw [RecursiveInterchangeScalingConstruct.input_target hs a t u]

theorem bound_linear (r : ℚ) (V : ℕ) (hV : 0 < V) :
    bound r V ≤ ((2+5*TapeCount r)*
      (2829+120*(r.num.natAbs+r.den)+22*RecursiveScalingInstall.LocalTapes r.num.natAbs r.den)+
      11*TapeCount r+4)*V := by
  unfold bound
  nlinarith [Nat.mul_le_mul_left ((2+5*TapeCount r)*401+11*TapeCount r+4) hV]

private theorem input_head {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) :
    (RecursiveInterchangeScalingConstruct.input (r := r) hs a t).head = TrackedInit.position (right r) := by
  funext i
  induction i using Fin.addCases with
  | left i => fin_cases i <;> rfl
  | right i =>
    simp only [RecursiveInterchangeScalingConstruct.input,Tapes.append,Fin.addCases_right]
    simp [RecursiveInterchangeScalingConstruct.workspace,RecursiveScalingInstall.lifted_head,TrackedInit.position,right]
    omega

private theorem input_private {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (i : Fin (TapeCount r)) (hi : keep r i = false) :
    (RecursiveInterchangeScalingConstruct.input (r := r) hs a t).head i = 0 ∧
    (RecursiveInterchangeScalingConstruct.input (r := r) hs a t).tape i = fun _ => blank := by
  induction i using Fin.addCases with
  | left i =>
    apply RecursiveInterchangeScalingConstruct.input_dimension_blank hs a t i
    simp only [keep,right,Bool.or_eq_false_iff,decide_eq_false_iff_not,Fin.val_castAdd] at hi
    exact hi.1
  | right i =>
    apply RecursiveInterchangeScalingConstruct.input_workspace_blank hs a t i
    intro he
    have hx := (FlatCoordinateScalingSharedBank.kinds_payload r i).mp he
    subst i
    simp [keep,sourceSlot] at hi

private theorem kept_cases (r : ℚ) (i : Fin (TapeCount r)) (hi : keep r i = true) :
    (∃ j : Fin 6, i = headerSlot r j) ∨ i = sourceSlot r ∨ i = destSlot r := by
  simp only [keep,right,Bool.or_eq_true,decide_eq_true_eq] at hi
  rcases hi with ⟨hlo,hhi⟩ | hi
  · left
    refine ⟨⟨i.val-3,by omega⟩,?_⟩
    apply Fin.ext
    simp [headerSlot]
    omega
  · exact Or.inr hi

private theorem kept_eq {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target)
    (i : Fin (TapeCount r)) (hi : keep r i = true) :
    (RecursiveInterchangeScalingConstruct.output hr hs a t).head i =
        (RecursiveInterchangeScalingConstruct.input (r := r) hs (RecursiveInterchangeScaling.array hr a t) t).head i ∧
    (RecursiveInterchangeScalingConstruct.output hr hs a t).tape i =
        (RecursiveInterchangeScalingConstruct.input (r := r) hs (RecursiveInterchangeScaling.array hr a t) t).tape i := by
  have hp := (RecursiveInterchangeScalingConstruct.output_payload hr hs a t).trans
    (RecursiveInterchangeScalingConstruct.input_payload hr hs (RecursiveInterchangeScaling.array hr a t) t).symm
  rcases kept_cases r i hi with ⟨j,rfl⟩ | rfl | rfl
  · have ho := RecursiveInterchangeScalingConstruct.headers_preserved hr hs a t j
    have hi := RecursiveInterchangeScalingConstruct.input_header (r := r) hs (RecursiveInterchangeScaling.array hr a t) t j
    exact ⟨ho.1.trans hi.1.symm,ho.2.trans hi.2.symm⟩
  · exact ⟨congrArg (fun w : Tapes 2 prime => w.head 0) hp,congrArg (fun w : Tapes 2 prime => w.tape 0) hp⟩
  · exact ⟨congrArg (fun w : Tapes 2 prime => w.head 1) hp,congrArg (fun w : Tapes 2 prime => w.tape 1) hp⟩

private theorem retained_eq {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :
    TrackedCleanupList.retained (keep r) (RecursiveInterchangeScalingConstruct.output hr hs a t) =
      RecursiveInterchangeScalingConstruct.input (r := r) hs (RecursiveInterchangeScaling.array hr a t) t := by
  apply congrArg₂ Tapes.mk
  · funext i
    cases hk : keep r i with
    | true => exact (kept_eq hr hs a t i hk).1
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveInterchangeScalingConstruct.input,Tapes.append]
        using (input_private hs (RecursiveInterchangeScaling.array hr a t) t i hk).1.symm
  · funext i
    cases hk : keep r i with
    | true => exact (kept_eq hr hs a t i hk).2
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveInterchangeScalingConstruct.input,Tapes.append]
        using (input_private hs (RecursiveInterchangeScaling.array hr a t) t i hk).2.symm

/-- A coefficient-dependent linear bound includes setup, execution, and cleanup. -/
theorem realizes_hoare {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hr t) (fun w => w = bank (r := r) hs a t)
      (fun w => w = bank (r := r) hs (RecursiveInterchangeScaling.array hr a t) t)
      (bound r (volume prime v)) := by
  have hh := CleanExecution.realizes (RecursiveInterchangeScalingConstruct.program hr t) (right r) (keep r)
    (RecursiveInterchangeScalingConstruct.input (r := r) hs a t) (RecursiveInterchangeScalingConstruct.output hr hs a t)
    _ (input_head hs a t) (fun i hi => (input_private hs a t i hi).2)
    (RecursiveInterchangeScalingConstruct.constructs_hoare hr hs a t hv hvpos)
  rw [retained_eq] at hh
  exact hh

theorem trackers_blank {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (i : Fin (TapeCount r)) :
    (bank (r := r) hs a t).head (Fin.natAdd (TapeCount r) i) = 0 ∧
    (bank (r := r) hs a t).tape (Fin.natAdd (TapeCount r) i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

theorem private_blank {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (i : Fin (TapeCount r)) (hi : keep r i = false) :
    (bank (r := r) hs a t).head (Fin.castAdd (TapeCount r) i) = 0 ∧
    (bank (r := r) hs a t).tape (Fin.castAdd (TapeCount r) i) = fun _ => blank := by
  simpa only [bank,Tapes.append,Fin.addCases_left] using input_private hs a t i hi

theorem payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target) :
    SharedPayload.payload (bank (r := r) hs a t) (Fin.castAdd (TapeCount r) (sourceSlot r))
      (Fin.castAdd (TapeCount r) (destSlot r)) = FlatAffineScalingPayload.pair a := by
  simpa only [bank,SharedPayload.payload,Tapes.append,Fin.addCases_left] using
    RecursiveInterchangeScalingConstruct.input_payload hr hs a t

theorem bank_head {v : Descriptor} {r : ℚ} (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (t : Target) :
    (bank (r := r) hs a t).head = Fin.addCases (TrackedInit.position (right r)) (fun _ => 0) := by
  unfold bank Tapes.append SharedBank.empty
  rw [input_head]

theorem realizes_array {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (t : Target)
    (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program hr t) (fun w => w = bank (r := r) hs a t)
      (fun w => w = bank (r := r) hs (RecursiveInterchangeScaling.array hr a t) t ∧
        SharedPayload.payload w (Fin.castAdd (TapeCount r) (sourceSlot r))
          (Fin.castAdd (TapeCount r) (destSlot r)) =
          FlatAffineScalingPayload.pair (RecursiveInterchangeScaling.array hr a t) ∧
        ∀ x : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeScaling.array hr a t
            (RecursiveInterchangeScaling.index (RecursiveInterchangeScaling.scaleAddress r x t)) =
              a (RecursiveInterchangeScaling.index x))
      (bound r (volume prime v)) := by
  apply (realizes_hoare hr hs a t hv hvpos).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,payload hr hs _ t,RecursiveInterchangeScaling.array_entry hr a t⟩

end
end IntegerMultBounds.Machine.RecursiveInterchangeScalingClean

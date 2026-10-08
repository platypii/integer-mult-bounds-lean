import IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule
import IntegerMultBounds.Machine.CleanExecution

/-! Fully reusable mixed affine schedules. The only nonblank input and output
are the permanent array/scratch/b/W bank; every generated work and tracking tape
is physically erased and returned to head zero at a linear-volume total cost. -/
namespace IntegerMultBounds.Machine.FlatCoordinateCleanSchedule
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateSchedule (Op)
open SharedBankStageInput (raw)
noncomputable section
variable {d b W : ℕ}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

def right {t : ℕ} (i : Fin t) : Bool := decide (i.val = 2 ∨ i.val = 3)
def keep {t : ℕ} (i : Fin t) : Bool := decide (i.val < 4)

def tapeCount (ops : List (Op d)) : ℕ :=
  (FlatCoordinateInitializedSchedule.skeleton ops).tapes+(FlatCoordinateInitializedSchedule.skeleton ops).tapes

def program (ops : List (Op d)) :=
  CleanExecution.program (FlatCoordinateInitializedSchedule.skeleton ops).program right keep

def constant (ops : List (Op d)) : ℕ :=
  (2+5*(FlatCoordinateInitializedSchedule.skeleton ops).tapes)*FlatCoordinateInitializedSchedule.constant ops+
    11*(FlatCoordinateInitializedSchedule.skeleton ops).tapes+4

private theorem raw_append_empty {k t a : ℕ} (c : Tapes k a) (hk : k ≤ t) :
    (raw c t).append (SharedBank.empty t a) = raw c (t+t) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp only [Fin.addCases_left,raw,Fin.val_castAdd]
  | right i =>
    have hn : ¬ (Fin.natAdd t i).val < k := by simp only [Fin.val_natAdd]; omega
    simp only [Fin.addCases_right,raw,hn,dite_false,SharedBank.empty]

private theorem retained_raw {t a : ℕ} (v : Tapes t a) (c : Tapes 4 a)
    (slots : Fin 4 → Fin t) (hs : ∀ i, (slots i).val = i.val)
    (hp : SharedBank.payload v slots = c) : TrackedCleanupList.retained keep v = raw c t := by
  have he (i : Fin t) (hi : i.val < 4) :
      v.head i = c.head ⟨i.val,hi⟩ ∧ v.tape i = c.tape ⟨i.val,hi⟩ := by
    let j : Fin 4 := ⟨i.val,hi⟩
    have hj : slots j = i := Fin.ext (hs j)
    have hh := congrFun (congrArg Tapes.head hp) j
    have ht := congrFun (congrArg Tapes.tape hp) j
    exact ⟨by simpa only [SharedBank.payload,hj] using hh,
      by simpa only [SharedBank.payload,hj] using ht⟩
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val < 4
    · simpa only [TrackedCleanupList.retained,keep,decide_eq_true hi,ite_true,raw,dite_eq_left hi] using (he i hi).1
    · simp [keep,hi]
  · funext i
    by_cases hi : i.val < 4
    · simpa only [TrackedCleanupList.retained,keep,decide_eq_true hi,ite_true,raw,dite_eq_left hi] using (he i hi).2
    · simp [keep,hi]

private theorem common_head (a : FlatCoordinateStages.Array d b W) (i : Fin 4) :
    (FlatCoordinateShiftSharedBank.common a).head i = if i.val = 2 ∨ i.val = 3 then 1 else 0 := by
  fin_cases i <;> rfl

private theorem input_head (ops : List (Op d)) (a : FlatCoordinateStages.Array d b W) :
    (FlatCoordinateInitializedSchedule.input ops b W a).head = TrackedInit.position right := by
  funext i
  by_cases hi : i.val < 4
  · simp only [FlatCoordinateInitializedSchedule.input,raw,dite_eq_left hi,common_head,
      TrackedInit.position,right,decide_eq_true_eq]
  · have hn : ¬ (i.val = 2 ∨ i.val = 3) := by omega
    simp [FlatCoordinateInitializedSchedule.input,raw,hi,TrackedInit.position,right,hn]

/-- One fixed machine, literal clean input and literal clean output, and exact
ordered affine transport at every coordinate and trailing record symbol. -/
theorem realizes (ops : List (Op d)) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array d b W) :
    HoareTime (program ops)
      (fun v => v = raw (FlatCoordinateShiftSharedBank.common a) (tapeCount ops))
      (fun v => v = raw (FlatCoordinateShiftSharedBank.common
        (FlatCoordinateInitializedSchedule.array ops b W hW a)) (tapeCount ops) ∧
        ∀ (x : Fin d → ZMod (modulus b)) (j : Fin W),
          FlatCoordinateInitializedSchedule.array ops b W hW a
            (FlatCoordinateLayout.index (Networks.OrderedAffine.run (ops.map (fun op => op.action b)) x) j) =
              a (FlatCoordinateLayout.index x j))
      (constant ops*((modulus b)^d*W)) := by
  obtain ⟨output,hh⟩ := FlatCoordinateInitializedSchedule.realizes ops b W hW
  have hexact := (hh a).consequence (fun _ h => h) (fun _ h => h.1) le_rfl
  have hcommon : SharedBank.payload (output a) (FlatCoordinateInitializedSchedule.skeleton ops).slots =
      FlatCoordinateShiftSharedBank.common (FlatCoordinateInitializedSchedule.array ops b W hW a) := by
    obtain ⟨_,c,_,_,_,hc⟩ := hh a _ rfl
    rw [hc.1] at hc
    exact hc.2.1
  have hclean := CleanExecution.realizes (FlatCoordinateInitializedSchedule.skeleton ops).program
    right keep (FlatCoordinateInitializedSchedule.input ops b W a) (output a)
    (FlatCoordinateInitializedSchedule.constant ops*((modulus b)^d*W)) (input_head ops a)
    (by
      intro i hi
      have hn : ¬ i.val < 4 := by simpa only [keep,decide_eq_false_iff_not] using hi
      simp only [FlatCoordinateInitializedSchedule.input,raw,dite_eq_right hn]) hexact
  apply hclean.consequence ?_ ?_ ?_
  · intro v hv
    exact hv.trans (raw_append_empty (FlatCoordinateShiftSharedBank.common a)
      (FlatCoordinateInitializedSchedule.skeleton_tapes_ge ops)).symm
  · intro v hv
    rw [retained_raw (output a) _ _ (FlatCoordinateInitializedSchedule.skeleton_slots_val ops) hcommon,
      raw_append_empty _ (FlatCoordinateInitializedSchedule.skeleton_tapes_ge ops)] at hv
    exact ⟨hv,FlatCoordinateInitializedSchedule.array_entry ops b W hW a⟩
  · have hV : 0 < (modulus b)^d*W := Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW
    unfold constant
    nlinarith

end
end IntegerMultBounds.Machine.FlatCoordinateCleanSchedule

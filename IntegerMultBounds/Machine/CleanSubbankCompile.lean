import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.SharedBankStageInput

/-! Finite physical joining of stages that clean their private outputs. Every
join is charged; the compiled input and output contain only the same permanent
bank and blank private tapes, ready for another caller or recursive continuation. -/
namespace IntegerMultBounds.Machine.CleanSubbankCompile
open SharedBankStage
universe u
variable {X : Type u} {k a : ℕ} {common : X → Tapes k a}
noncomputable section

def Clean (s : Stage X k a common) : Prop :=
  ∀ x, SharedBank.strip (s.output x) s.slots = SharedBank.empty s.tapes a

theorem identity_clean (hk : 0 < k) : Clean (identity common hk) :=
  fun x => SharedBankFrames.strip_identity (common x)

theorem compose_clean (s r : Stage X k a common) (hs : Clean s) (hr : Clean r) :
    Clean (compose s r) := by
  intro x
  change SharedBank.strip (SharedBankPair.output (s.output x) (r.output (s.transform x)) s.slots r.slots)
    (SharedBankFrames.commonSlots k s.tapes r.tapes) = _
  rw [SharedBankPair.output,SharedBankFrames.strip_common,hs,hr,
    SharedBankFrames.empty_append,SharedBankFrames.empty_append]
  rfl

theorem compile_clean (hk : 0 < k) (ss : List (Stage X k a common))
    (hc : ∀ s ∈ ss, Clean s) : Clean (compile common hk ss) := by
  induction ss with
  | nil => exact identity_clean hk
  | cons s ss ih =>
    exact compose_clean s _ (hc s (by simp)) (ih (fun r hr => hc r (by simp [hr])))

theorem output_raw (hk : 0 < k) (ss : List (Stage X k a common))
    (hc : ∀ s ∈ ss, Clean s) (x : X) :
    (compile common hk ss).output x =
      SharedBankStageInput.raw (common (execute ss x)) (compile common hk ss).tapes := by
  apply SharedBankStageInput.eq_raw _ _ _ (SharedBankStageInput.compile_slots_val hk ss)
  · rw [(compile common hk ss).output_payload,compile_transform]
  · exact compile_clean hk ss hc x

/-- Complete clean-to-clean execution of the actual finite joined machine.
This theorem applies to arbitrary permanent banks and heterogeneous local layouts. -/
theorem realizes (hk : 0 < k) (ss : List (Stage X k a common))
    (hi : ∀ s ∈ ss, s.metadata = SharedBank.empty s.tapes a)
    (hc : ∀ s ∈ ss, Clean s) (x : X) :
    HoareTime (compile common hk ss).program
      (fun v => v = SharedBankStageInput.raw (common x) (compile common hk ss).tapes)
      (fun v => v = SharedBankStageInput.raw (common (execute ss x)) (compile common hk ss).tapes)
      ((ss.map Stage.cost).sum+ss.length) := by
  apply (compile_hoare hk ss x).consequence ?_ ?_ le_rfl
  · intro v hv
    exact hv.trans (SharedBankStageInput.compile_input_raw hk ss hi x).symm
  · intro v hv
    exact hv.1.trans (output_raw hk ss hc x)

end
end IntegerMultBounds.Machine.CleanSubbankCompile

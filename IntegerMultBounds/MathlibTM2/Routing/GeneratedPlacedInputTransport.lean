module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInput
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreMetadata

/-! Readiness and framed metadata transport across record replacements and external cursors. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "ep₀" => inactiveClassifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => inactiveClassifierPlacementSlot (t₀ := t₀)

/-- Input and output cursors are external to the generated call's readiness data. -/
noncomputable def GeneratedPlacedInput.withIO (input : GeneratedPlacedInput t₀ Q K P P' U)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : GeneratedPlacedInput t₀ Q K P P' U := by
  refine { input with
    S := { input.S with inp := inp, out := out }
    D := { input.D with inp := inp, out := out }
    E := { input.E with inp := inp, out := out }
    F := { input.F with inp := inp, out := out }
    M := { input.M with inp := inp, out := out }
    hproject := ?_
    hE := ?_
    hF := ?_
    houterProject := ?_ }
  · have h := congrArg (fun S => { S with inp := inp, out := out }) input.hproject
    dsimp only [embStk] at h ⊢
    exact h
  · have h := congrArg (fun S => { S with inp := inp, out := out }) input.hE
    dsimp only [embStk] at h ⊢
    exact h
  · have h := congrArg (fun S => { S with inp := inp, out := out }) input.hF
    dsimp only [embStk] at h ⊢
    exact h
  · have h := congrArg (fun S => { S with inp := inp, out := out }) input.houterProject
    dsimp only [embStk] at h ⊢
    exact h

/-- Readiness depends on record shape, but not on the values or order of records. -/
noncomputable def GeneratedPlacedInput.replaceRecords (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8) :
    GeneratedPlacedInput t₀ Q K P P' U := by
  let S₀ : Stacks T₀ (prime + K) := { input.S with R := Function.update input.S.R (inactiveProfileRaw repairHost.src) l.flatten }
  let D₀ : Stacks inactiveProfileHeaderT (prime + K) := { input.D with R := Function.update input.D.R (inactiveProfileHeaderRaw repairHost.src) l.flatten }
  let E₀ : Stacks inactiveProfileConfigurationT (prime + K) := { input.E with R := Function.update input.E.R (inactiveConfigurationCore repairHost.src) l.flatten }
  let F₀ : Stacks inactiveClassifierT (prime + K) := { input.F with R := Function.update input.F.R (classifierCore (inactiveConfigurationCore repairHost.src)) l.flatten }
  let M₀ : Stacks TP₀ (prime + K) := { input.M with R := Function.update input.M.R (ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))) l.flatten }
  have hkeep (i : Fin T₀) (hi : i ≠ inactiveProfileRaw repairHost.src) : S₀.R i = input.S.R i := by
    dsimp only [S₀]
    exact Function.update_of_ne hi _ _
  have hdkeep (i : Fin inactiveProfileHeaderT) (hi : i ≠ inactiveProfileHeaderRaw repairHost.src) : D₀.R i = input.D.R i := by
    dsimp only [D₀]
    exact Function.update_of_ne hi _ _
  have hekeep (i : Fin inactiveProfileConfigurationT) (hi : i ≠ inactiveConfigurationCore repairHost.src) : E₀.R i = input.E.R i := by
    dsimp only [E₀]
    exact Function.update_of_ne hi _ _
  have hfkeep (i : Fin inactiveClassifierT) (hi : i ≠ classifierCore (inactiveConfigurationCore repairHost.src)) : F₀.R i = input.F.R i := by
    dsimp only [F₀]
    exact Function.update_of_ne hi _ _
  have haux (r : LiveDescriptorRole 11) : S₀.R (e₀ (liveDescriptorAux r)) = input.S.R (e₀ (liveDescriptorAux r)) :=
    hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux repairHost.src r).symm)
  have hpaux (i : Fin 7) : S₀.R (liveInactiveProfileAux i) = input.S.R (liveInactiveProfileAux i) := hkeep _ (liveInactiveProfileAux_core _ _)
  have hhwork (r : HeaderWorkRole) : D₀.R (sharedHeaderWork r) = input.D.R (sharedHeaderWork r) := hdkeep _ (sharedHeaderCore_work _ r).symm
  have heaux (i : Fin 6) : E₀.R (fieldAux i) = input.E.R (fieldAux i) := hekeep _ (fieldCore_aux _ i).symm
  have hfaux (i : Fin 16) : F₀.R (classifierAux i) = input.F.R (classifierAux i) := hfkeep _ (classifierCore_aux _ i).symm
  refine { input with
    S := S₀
    D := D₀
    E := E₀
    F := F₀
    M := M₀
    l := l
    hl := hl
    hlen := hlen
    data := by
      apply input.data.congr input.p input.X input.rb
      intro key
      exact hkeep _ (inactiveProfileRaw_injective.ne (repairSetup_source_src key))
    hempty := fun key => (hkeep _ (inactiveProfileRaw_injective.ne (repairSetup_target_src key))).trans (input.hempty key)
    hL := input.hL
    hblank := fun j hj => (hkeep _ (inactiveProfileRaw_injective.ne (repairBlank_src j hj))).trans (input.hblank j hj)
    hbank := fun r hr => (haux r).trans (input.hbank r hr)
    hdesc := by
      intro d
      have hne : repairDescriptorSource d ≠ repairHost.src := by
        rw [repairDescriptorSource_eq]
        exact repairSetup_source_src _
      exact (hkeep _ (inactiveProfileRaw_injective.ne hne)).trans (input.hdesc d)
    hinput := fun j => (haux (.input j)).trans (input.hinput j)
    hkey := (hkeep _ (inactiveProfileRaw_injective.ne input.hkeySrc)).trans input.hkey
    hrawBlank := (hkeep _ (inactiveProfileRaw_injective.ne input.hrawSrc)).trans input.hrawBlank
    hactivity := (hkeep _ (inactiveProfileRaw_injective.ne input.hactivitySrc)).trans input.hactivity
    hcount := (hpaux 0).trans input.hcount
    hscratch := fun i hi => (hpaux i).trans (input.hscratch i hi)
    hsrc := by simp [S₀, inactiveProfileRaw]
    hproject := by
      dsimp only [D₀, S₀, inactiveProfileHeaderRaw, embeddedRepairHeaderRaw]
      rw [embStk_update_stream sharedHeaderCore sharedHeaderCore_injective, input.hproject]
    hrowInput := (hhwork (.binary 0)).trans input.hrowInput
    hwidthInput := (hhwork (.binary 1)).trans input.hwidthInput
    hwork := fun r hr => (hhwork r).trans (input.hwork r hr)
    hE := by
      dsimp only [E₀, D₀, inactiveConfigurationCore]
      rw [embStk_update_stream fieldCore fieldCore_injective, input.hE]
    hrowWidth := (heaux 0).trans input.hrowWidth
    hmaskWidth := (heaux 1).trans input.hmaskWidth
    hwidthScratch := fun i hi => (heaux i).trans (input.hwidthScratch i hi)
    hrow := (hekeep _ (inactiveConfigurationSource_src (.inr .row))).trans input.hrow
    hmask := (hekeep _ (inactiveConfigurationSource_src (.inr .keyMask))).trans input.hmask
    hF := by
      dsimp only [F₀, E₀]
      rw [embStk_update_stream classifierCore classifierCore_injective, input.hF]
    hsegmentInput := (hfaux 0).trans input.hsegmentInput
    hrunInput := (hfaux 1).trans input.hrunInput
    hcountInput := (hfaux 10).trans input.hcountInput
    hoffsetInput := (hfaux 13).trans input.hoffsetInput
    hphaseOffsetInput := (hfaux 14).trans input.hphaseOffsetInput
    htopInput := (hfaux 15).trans input.htopInput
    hclassifierScratch := fun i hi hn ht => (hfaux i).trans (input.hclassifierScratch i hi hn ht)
    htemporary := (hfkeep _ (classifierCore_injective.ne inactiveClassifierTemporary_src)).trans input.htemporary
    hphase := (hfkeep _ (classifierCore_injective.ne inactiveClassifierPhase_src)).trans input.hphase
    houterProject := by
      dsimp only [M₀, F₀]
      rw [embStk_update_stream ep₀ inactiveClassifierPlacementEmbed_injective, input.houterProject]
    hleft := input.hleft
    hplacementBank := by
      dsimp only [M₀, F₀]
      rw [sharedScheduleInputBank_updateStream _ _ _ _ _ _ _ _ input.l.flatten, input.hplacementBank]
      rfl
  }

/-- The same encoded call metadata works for every record stream of this shape. -/
theorem GeneratedPlacedInput.replaceRecords_jobs
    (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)
    {T : ℕ} (e : Fin TP₀ → Fin T) :
    framedCoreJobs e (ep₀ (classifierCore (inactiveConfigurationCore repairHost.src)))
        (input.replaceRecords l hl hlen).M.R =
      framedCoreJobs e (ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))) input.M.R := by
  dsimp only [GeneratedPlacedInput.replaceRecords]
  exact framedCoreJobs_updateStream _ _ _ _

end
end IntegerMultBounds.MathlibTM2.Routing

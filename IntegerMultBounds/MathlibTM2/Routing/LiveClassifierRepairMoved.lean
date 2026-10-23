module

public import IntegerMultBounds.MathlibTM2.Routing.LiveClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierInputFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Transport the generated-input live repair path across record placement.
All scalar, profile and workspace readiness follows from the original bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {Q K : ℕ} {P U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem liveClassifierRepairMoved_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (headerBody : P → Pr P repairLiveHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (liveBody f))
    (outerBody : P → Pr P liveHeaderConfigurationT Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg (fieldCore (N := repairLiveHeaderT)) id (headerBody f))
    (classifierBody : P → Pr P liveClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (outerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (w : LiveDescriptorWidths)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS liveClassifierT Q (prime + K) U) (S : Stacks liveHeaderConfigurationT (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (fieldCore (repairLiveHeaderRaw i))))
    (hready : LiveDescriptorReady p₀ X hG₀ hK₀ active s repairLiveMode w (fun i => S.R (fieldCore (sharedHeaderCore i))))
    (hempty : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (fieldCore (repairLiveHeaderRaw j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (fieldCore (repairLiveHeaderRaw j)) = [])
    (hdesc : ∀ key, S.R (fieldCore (repairLiveHeaderRaw (repairDescriptorSource key))) = [])
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : S.R (fieldCore (sharedHeaderBinary 0)) = binSyms Lrow R)
    (hwidthInput : S.R (fieldCore (sharedHeaderBinary 1)) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (fieldCore (sharedHeaderWork r)) = [])
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : S.R (fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (_hsrc : S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) = l.flatten)
    (D : Stacks liveClassifierT (prime + K)) (hproject : embStk classifierCore D = S)
    (LK Ln Lo Lt : ℕ) (hsegment : (p₀).K < 2 ^ LK) (hcount : n < 2 ^ Ln)
    (hoffset : ρ + 1 < 2 ^ Lo) (htop : m < 2 ^ Lt)
    (hsegmentInput : D.R (classifierAux 0) = binSyms LK (p₀).K)
    (hrunInput : D.R (classifierAux 1) = binSyms LK (p₀).G)
    (hcountInput : D.R (classifierAux 10) = binSyms Ln n)
    (hoffsetInput : D.R (classifierAux 13) = binSyms Lo (ρ + 1))
    (hphaseOffsetInput : D.R (classifierAux 14) = binSyms Lo ρ)
    (htopInput : D.R (classifierAux 15) = binSyms Lt m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → D.R (classifierAux i) = [])
    (htemporary : D.R (classifierCore liveClassifierTemporary) = [])
    (hphase : D.R (classifierCore liveClassifierPhase) = [])
    (π : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)))) :
    let l₁ := moveRecs π l
    let S₁ : Stacks liveHeaderConfigurationT (prime + K) := { S with R := Function.update S.R (liveHeaderConfigurationCore repairHost.src) l₁.flatten }
    let D₁ : Stacks liveClassifierT (prime + K) := { D with R := Function.update D.R (classifierCore (liveHeaderConfigurationCore repairHost.src)) l₁.flatten }
    let M : Stacks liveHeaderConfigurationT (prime + K) := { S₁ with R := liveHeaderConfigurationClassifierBank p₀ S₁.R }
    let W : Stacks liveHeaderConfigurationT (prime + K) := { M with R := liveHeaderWidthBank rb (p₀).wy M.R }
    let C := embStk (fieldCore (N := repairLiveHeaderT)) W
    ∃ (v' : HS liveClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (binaryTemporaryMaskCost p₀ LK Ln Lo Lt + binaryPhaseMaskCost p₀ LK Ln Lo Lt : ℕ) +
        ((((Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) : ℝ) +
        liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C +
        (2 * rb + 2 * (p₀).wy + 5 : ℕ)) + (4 * ((p₀).wy + 1) + 5 : ℕ) ∧
      Exec classifierBody (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat liveClassifierTemporary liveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (liveHeaderWidthJobs Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := repairLiveHeaderT)) id (liveHeaderRepairProgram hQ hA))
          (metadataClean [fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (repairLiveHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore liveClassifierTemporary, classifierCore liveClassifierPhase])))
        (mk v D₁) steps
        (mk v' { D₁ with R := Function.update D₁.R (classifierCore (liveHeaderConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₁).flatten }) := by
  let l₁ := moveRecs π l
  let S₁ : Stacks liveHeaderConfigurationT (prime + K) := { S with R := Function.update S.R (liveHeaderConfigurationCore repairHost.src) l₁.flatten }
  let D₁ : Stacks liveClassifierT (prime + K) := { D with R := Function.update D.R (classifierCore (liveHeaderConfigurationCore repairHost.src)) l₁.flatten }
  have hkeep (i : Fin liveHeaderConfigurationT) (hi : i ≠ liveHeaderConfigurationCore repairHost.src) : S₁.R i = S.R i := by
    dsimp only [S₁]
    exact Function.update_of_ne hi _ _
  have hdkeep (i : Fin liveClassifierT) (hi : i ≠ classifierCore (liveHeaderConfigurationCore repairHost.src)) : D₁.R i = D.R i := by
    dsimp only [D₁]
    exact Function.update_of_ne hi _ _
  have haux (i : Fin 6) : S₁.R (fieldAux i) = S.R (fieldAux i) :=
    hkeep _ (fieldCore_aux _ i).symm
  have hworkKeep (r : HeaderWorkRole) : S₁.R (fieldCore (sharedHeaderWork r)) = S.R (fieldCore (sharedHeaderWork r)) :=
    hkeep _ (fieldCore_injective.ne (sharedHeaderCore_work _ r).symm)
  have hdaux (i : Fin 16) : D₁.R (classifierAux i) = D.R (classifierAux i) :=
    hdkeep _ (classifierCore_aux _ i).symm
  apply liveClassifierRepair_exec ρ n m X rb scale active s body liveBody hlive headerBody hheader
    outerBody houter classifierBody hclassifier Lr Lm hr hm w hQ hA hscale hn hR hB hrb hs v S₁
  · apply data.congr p₀ X rb
    intro key
    exact hkeep _ (liveHeaderConfigurationCore_injective.ne (repairSetup_source_src key))
  · refine ⟨hready.bounds, ?_⟩
    intro r
    rw [hkeep _ (fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveDescriptorCore_aux repairHost.src r).symm))]
    exact hready.bank r
  · intro key
    exact (hkeep _ (liveHeaderConfigurationCore_injective.ne (repairSetup_target_src key))).trans (hempty key)
  · exact hL
  · intro j hj
    exact (hkeep _ (liveHeaderConfigurationCore_injective.ne (repairBlank_src j hj))).trans (hblank j hj)
  · intro key
    have hne : repairDescriptorSource key ≠ repairHost.src := by
      rw [repairDescriptorSource_eq]
      exact repairSetup_source_src _
    exact (hkeep _ (liveHeaderConfigurationCore_injective.ne hne)).trans (hdesc key)
  · exact hRfit
  · exact hwidthFit
  · exact (hworkKeep (.binary 0)).trans hrowInput
  · exact (hworkKeep (.binary 1)).trans hwidthInput
  · intro r hr
    exact (hworkKeep r).trans (hwork r hr)
  · exact (haux 0).trans hrowWidth
  · exact (haux 1).trans hmaskWidth
  · intro i hi
    exact (haux i).trans (hwidthScratch i hi)
  · exact (hkeep _ (liveHeaderConfigurationSource_src (.inr .row))).trans hrow
  · exact (hkeep _ (liveHeaderConfigurationSource_src (.inr .keyMask))).trans hmask
  · exact length_moveRecs π l
  · intro r hr
    exact hlen r (mem_moveRecs π hl hr)
  · simp [S₁, liveHeaderConfigurationCore, l₁]
  · dsimp only [D₁, S₁]
    rw [embStk_update_stream classifierCore classifierCore_injective, hproject]
  · exact hsegment
  · exact hcount
  · exact hoffset
  · exact htop
  · exact (hdaux 0).trans hsegmentInput
  · exact (hdaux 1).trans hrunInput
  · exact (hdaux 10).trans hcountInput
  · exact (hdaux 13).trans hoffsetInput
  · exact (hdaux 14).trans hphaseOffsetInput
  · exact (hdaux 15).trans htopInput
  · intro i hi hn ht
    exact (hdaux i).trans (hclassifierScratch i hi hn ht)
  · exact (hdkeep _ (classifierCore_injective.ne liveClassifierTemporary_src)).trans htemporary
  · exact (hdkeep _ (classifierCore_injective.ne liveClassifierPhase_src)).trans hphase

end
end IntegerMultBounds.MathlibTM2.Routing

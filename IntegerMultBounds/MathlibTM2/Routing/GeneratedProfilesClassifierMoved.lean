module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedProfilesClassifierRepair
public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierInputFrame

/-! Record placement preserves the scalar/profile inputs and every readiness
condition of the complete generated-input repair path. -/

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
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

theorem generatedProfilesClassifierMoved_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (Lc : ℕ) (hnfit : n < 2 ^ Lc)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveClassifierT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairGeneratedProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j ∈ repairGeneratedProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (_hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p₀).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p₀).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D)
    (widthBody : P → Pr P inactiveProfileConfigurationT Q (prime + K) U)
    (hwidthBody : ∀ f, widthBody f = embProg (fieldCore (N := inactiveProfileHeaderT)) id (headerBody f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : (p₀).wy < 2 ^ Lm)
    (hrowWidth : E.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : E.R (fieldAux 1) = binSyms Lm (p₀).wy)
    (hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → E.R (fieldAux i) = [])
    (hrow : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))) = [])
    (hmask : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))) = [])
    (classifierBody : P → Pr P inactiveClassifierT Q (prime + K) U)
    (hclassifier : ∀ f, classifierBody f = embProg classifierCore id (widthBody f))
    (F : Stacks inactiveClassifierT (prime + K)) (hF : embStk classifierCore F = E)
    (LK Ln Lo Lt : ℕ) (hsegment : (p₀).K < 2 ^ LK) (hcountFit : n < 2 ^ Ln)
    (hoffset : ρ + 1 < 2 ^ Lo) (htop : m < 2 ^ Lt)
    (hsegmentInput : F.R (classifierAux 0) = binSyms LK (p₀).K)
    (hrunInput : F.R (classifierAux 1) = binSyms LK (p₀).G)
    (hcountInput : F.R (classifierAux 10) = binSyms Ln n)
    (hoffsetInput : F.R (classifierAux 13) = binSyms Lo (ρ + 1))
    (hphaseOffsetInput : F.R (classifierAux 14) = binSyms Lo ρ)
    (htopInput : F.R (classifierAux 15) = binSyms Lt m)
    (hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → F.R (classifierAux i) = [])
    (htemporary : F.R (classifierCore inactiveClassifierTemporary) = [])
    (hphase : F.R (classifierCore inactiveClassifierPhase) = [])
    (π : Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p₀ X)))) :
    let l₀ := moveRecs π l
    let E₀ : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) l₀.flatten }
    let F₀ : Stacks inactiveClassifierT (prime + K) := { F with R := Function.update F.R (classifierCore (inactiveConfigurationCore repairHost.src)) l₀.flatten }
    let E₁ : Stacks inactiveProfileConfigurationT (prime + K) := { E₀ with R := inactiveConfigurationClassifierBank p₀ E₀.R }
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E₁ with R := inactiveProfileWidthBank rb (p₀).wy E₁.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairGeneratedProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveClassifierT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (binaryTemporaryMaskCost p₀ LK Ln Lo Lt + binaryPhaseMaskCost p₀ LK Ln Lo Lt : ℕ) +
        (((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        ((2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        (((3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits n + 1) + binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits n : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (4 * (2 * (n * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ)) + (2 * rb + 2 * (p₀).wy + 5 : ℕ)) + (4 * ((p₀).wy + 1) + 5 : ℕ) ∧
      Exec classifierBody (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq repairGeneratedProfilesProgram
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairGeneratedProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore inactiveClassifierTemporary, classifierCore inactiveClassifierPhase])))
        (mk v F₀) steps
        (mk v' { F₀ with R := Function.update F₀.R (classifierCore (inactiveConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₀).flatten }) := by
  let l₀ := moveRecs π l
  let S₀ : Stacks T₀ (prime + K) := { S with R := Function.update S.R (inactiveProfileRaw repairHost.src) l₀.flatten }
  let D₀ : Stacks inactiveProfileHeaderT (prime + K) := { D with R := Function.update D.R (inactiveProfileHeaderRaw repairHost.src) l₀.flatten }
  let E₀ : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) l₀.flatten }
  let F₀ : Stacks inactiveClassifierT (prime + K) := { F with R := Function.update F.R (classifierCore (inactiveConfigurationCore repairHost.src)) l₀.flatten }
  have hkeep (i : Fin T₀) (hi : i ≠ inactiveProfileRaw repairHost.src) : S₀.R i = S.R i := by
    dsimp only [S₀]
    exact Function.update_of_ne hi _ _
  have hdkeep (i : Fin inactiveProfileHeaderT) (hi : i ≠ inactiveProfileHeaderRaw repairHost.src) : D₀.R i = D.R i := by
    dsimp only [D₀]
    exact Function.update_of_ne hi _ _
  have hekeep (i : Fin inactiveProfileConfigurationT) (hi : i ≠ inactiveConfigurationCore repairHost.src) : E₀.R i = E.R i := by
    dsimp only [E₀]
    exact Function.update_of_ne hi _ _
  have hfkeep (i : Fin inactiveClassifierT) (hi : i ≠ classifierCore (inactiveConfigurationCore repairHost.src)) : F₀.R i = F.R i := by
    dsimp only [F₀]
    exact Function.update_of_ne hi _ _
  have haux (r : LiveDescriptorRole 11) : S₀.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) :=
    hkeep _ (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux repairHost.src r).symm)
  have hpaux (i : Fin 7) : S₀.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := hkeep _ (liveInactiveProfileAux_core _ _)
  have hhwork (r : HeaderWorkRole) : D₀.R (sharedHeaderWork r) = D.R (sharedHeaderWork r) := hdkeep _ (sharedHeaderCore_work _ r).symm
  have heaux (i : Fin 6) : E₀.R (fieldAux i) = E.R (fieldAux i) := hekeep _ (fieldCore_aux _ i).symm
  have hfaux (i : Fin 16) : F₀.R (classifierAux i) = F.R (classifierAux i) := hfkeep _ (classifierCore_aux _ i).symm
  apply generatedProfilesClassifierRepair_exec ρ n m X rb scale active s body liveBody hlive outerBody houter
    Lc hnfit w hwidth hQ hA hscale hn hR hB hrb hs v S₀
  · apply data.congr p₀ X rb
    intro key
    exact hkeep _ (inactiveProfileRaw_injective.ne (repairSetup_source_src key))
  · intro key
    exact (hkeep _ (inactiveProfileRaw_injective.ne (repairSetup_target_src key))).trans (hempty key)
  · exact hL
  · intro j hj
    exact (hkeep _ (inactiveProfileRaw_injective.ne (repairBlank_src j hj))).trans (hblank j hj)
  · exact hfit
  · intro r hr
    exact (haux r).trans (hbank r hr)
  · intro d
    have hne : repairDescriptorSource d ≠ repairHost.src := by
      rw [repairDescriptorSource_eq]
      exact repairSetup_source_src _
    exact (hkeep _ (inactiveProfileRaw_injective.ne hne)).trans (hdesc d)
  · intro j hj
    exact (haux (.input j)).trans (hinput j hj)
  · exact (hpaux 0).trans hcount
  · intro i hi
    exact (hpaux i).trans (hscratch i hi)
  · exact length_moveRecs π l
  · intro r hr
    exact hlen r (mem_moveRecs π hl hr)
  · simp [S₀, inactiveProfileRaw, l₀]
  · dsimp only [D₀, S₀, inactiveProfileHeaderRaw, embeddedRepairHeaderRaw]
    rw [embStk_update_stream sharedHeaderCore sharedHeaderCore_injective, hproject]
  · exact hheader
  · exact hRfit
  · exact hwidthFit
  · exact (hhwork (.binary 0)).trans hrowInput
  · exact (hhwork (.binary 1)).trans hwidthInput
  · intro r hr
    exact (hhwork r).trans (hwork r hr)
  · dsimp only [E₀, D₀, inactiveConfigurationCore]
    rw [embStk_update_stream fieldCore fieldCore_injective, hE]
    rfl
  · exact hwidthBody
  · exact hr
  · exact hm
  · exact (heaux 0).trans hrowWidth
  · exact (heaux 1).trans hmaskWidth
  · intro i hi
    exact (heaux i).trans (hwidthScratch i hi)
  · exact (hekeep _ (inactiveConfigurationSource_src (.inr .row))).trans hrow
  · exact (hekeep _ (inactiveConfigurationSource_src (.inr .keyMask))).trans hmask
  · exact hclassifier
  · try dsimp only [F₀, E₀]
    rw [embStk_update_stream classifierCore classifierCore_injective, hF]
  · exact hsegment
  · exact hcountFit
  · exact hoffset
  · exact htop
  · exact (hfaux 0).trans hsegmentInput
  · exact (hfaux 1).trans hrunInput
  · exact (hfaux 10).trans hcountInput
  · exact (hfaux 13).trans hoffsetInput
  · exact (hfaux 14).trans hphaseOffsetInput
  · exact (hfaux 15).trans htopInput
  · intro i hi hn ht
    exact (hfaux i).trans (hclassifierScratch i hi hn ht)
  · exact (hfkeep _ (classifierCore_injective.ne inactiveClassifierTemporary_src)).trans htemporary
  · exact (hfkeep _ (classifierCore_injective.ne inactiveClassifierPhase_src)).trans hphase

end
end IntegerMultBounds.MathlibTM2.Routing

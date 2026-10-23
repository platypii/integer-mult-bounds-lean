module

public import IntegerMultBounds.MathlibTM2.Routing.LiveClassifierRepairGenerated
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate classifier masks, execute width/header/live-descriptor repair and
erase masks. Every phase is charged and only the record stream changes. -/

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

theorem liveClassifierRepair_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (hsrc : S.R (fieldCore (repairLiveHeaderRaw repairHost.src)) = l.flatten)
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
    (hphase : D.R (classifierCore liveClassifierPhase) = []) :
    let M : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderConfigurationClassifierBank p₀ S.R }
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
        (mk v D) steps
        (mk v' { D with R := Function.update D.R (classifierCore (liveHeaderConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let M : Stacks liveHeaderConfigurationT (prime + K) := { S with R := liveHeaderConfigurationClassifierBank p₀ S.R }
  let W : Stacks liveHeaderConfigurationT (prime + K) := { M with R := liveHeaderWidthBank rb (p₀).wy M.R }
  let C := embStk (fieldCore (N := repairLiveHeaderT)) W
  apply classifierBankRepair_exec classifierBody outerBody hclassifier _ p₀ hG₀
    (routingParameters_guards ρ n m (Nat.clog 2 scale)).2.2
    liveClassifierTemporary liveClassifierPhase liveClassifierOutputs_ne
    LK Ln Lo Lt hsegment hcount hoffset htop v D
    hsegmentInput hrunInput hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase
    (liveHeaderConfigurationCore repairHost.src) liveClassifierTemporary_src liveClassifierPhase_src
    (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten
    (((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
      liveHeaderRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B Lrow Lwidth w C +
      (2 * rb + 2 * (p₀).wy + 5 : ℕ))
  intro u
  dsimp only
  have hp := liveClassifierBank_project (A := prime + K) p₀ D
  rw [hproject] at hp
  rw [hp]
  exact liveClassifierRepairGenerated_exec ρ n m X rb scale active s body liveBody hlive
    headerBody hheader outerBody houter Lr Lm hr hm w hQ hA hscale hn hR hB hrb hs u S
    data hready hempty hL hblank hdesc Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork
    hrowWidth hmaskWidth hwidthScratch hrow hmask l hl hlen hsrc

end
end IntegerMultBounds.MathlibTM2.Routing

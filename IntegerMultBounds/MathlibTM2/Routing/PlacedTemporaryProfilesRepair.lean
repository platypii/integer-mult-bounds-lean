module

public import IntegerMultBounds.MathlibTM2.Routing.TemporaryProfilesClassifierMoved
public import IntegerMultBounds.MathlibTM2.Routing.PlacementAround

/-! Execute reservoir placement, the full generated-input repair path and inverse
placement. All non-stream tapes are restored and every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {t₀ T Q K : ℕ} {P P' U : Type}
variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

theorem placedTemporaryProfilesRepair_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (activity : Fin repairT) (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (hactivityBadMask : activity ≠ repairSetupSource (.inr .badMask))
    (hactivityBadPhase : activity ≠ repairSetupSource (.inr .badPhase))
    (hactivitySrc : activity ≠ repairHost.src)
    (Lc : ℕ) (hnfit : n < 2 ^ Lc)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingMaskData p₀ X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairTemporaryProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j ∈ repairTemporaryProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hactivity : S.R (liveZSourceActivity activity) = (List.ofFn active).map bitSymbol)
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
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
    (e : Fin inactiveClassifierT → Fin T) (he : Function.Injective e) (ι : P → P')
    (placementBody : P' → Pr P' T Q (prime + K) U)
    (hplacementBody : ∀ f, placementBody (ι f) = embProg e ι (classifierBody f))
    (M : Stacks T (prime + K)) (hM : embStk e M = F)
    (tmp : Fin T) (Hslot : ℕ) (hplacementFit : 9 * Hslot ≤ fieldsLen (selectiveLen p₀ X))
    (slotWidth : ℕ) (hslotWidth : slotWidth ≤ Hslot) (reservoir : Fin 3)
    (calls : Fin 3 → BinaryExchangeCall t₀ T Q (fieldsLen (selectiveLen p₀ X)) R B
      (e (classifierCore (inactiveConfigurationCore repairHost.src))) tmp)
    (hspec : ∀ j, (calls j).spec = reservoirExchangeSpecs (fieldsLen (selectiveLen p₀ X)) Hslot hplacementFit slotWidth hslotWidth reservoir j)
    (hplacement : ∀ j, (calls j).Ready M)
    (houterSrc : M.R (e (classifierCore (inactiveConfigurationCore repairHost.src))) = l.flatten) :
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) Hslot hplacementFit slotWidth hslotWidth reservoir R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) Hslot hplacementFit slotWidth hslotWidth reservoir R true
    let l₀ := moveRecs forward l
    let E₀ : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) l₀.flatten }
    let E₁ : Stacks inactiveProfileConfigurationT (prime + K) := { E₀ with R := inactiveConfigurationClassifierBank p₀ E₀.R }
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E₁ with R := inactiveProfileWidthBank rb (p₀).wy E₁.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairTemporaryProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ binaryExchangeChainCost calls M (reservoirExchangeOrder false) +
        ((binaryTemporaryMaskCost p₀ LK Ln Lo Lt + binaryPhaseMaskCost p₀ LK Ln Lo Lt : ℕ) +
        (((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        ((2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        ((repairTemporaryProfilesCost p₀ w Lc : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (7 * (2 * (n * (w.selectorBits + 3)) + 2) + (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ)) + (2 * rb + 2 * (p₀).wy + 5 : ℕ)) + (4 * ((p₀).wy + 1) + 5 : ℕ)) + binaryExchangeChainCost calls M (reservoirExchangeOrder true) ∧
      Exec placementBody (.seq (binaryExchangeChain calls (reservoirExchangeOrder false))
        (.seq (embProg e ι (.seq (classifierPairProgram classifierBankReg
          (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) classifierBankPad)
        (.seq (embProg classifierCore id (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (repairTemporaryProfilesProgram activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairTemporaryProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))]))))
          (metadataClean [classifierCore inactiveClassifierTemporary, classifierCore inactiveClassifierPhase])))) (binaryExchangeChain calls (reservoirExchangeOrder true))))
        (mk v M) steps
        (mk v' { M with R := Function.update M.R (e (classifierCore (inactiveConfigurationCore repairHost.src))) (moveRecs backward (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₀)).flatten }) := by
  let forward := reservoirExchangeAction (fieldsLen (selectiveLen p₀ X)) Hslot hplacementFit slotWidth hslotWidth reservoir R false
  let l₀ := moveRecs forward l
  let F₀ : Stacks inactiveClassifierT (prime + K) := { F with R := Function.update F.R (classifierCore (inactiveConfigurationCore repairHost.src)) l₀.flatten }
  let M₀ : Stacks T (prime + K) := { M with R := Function.update M.R (e (classifierCore (inactiveConfigurationCore repairHost.src))) l₀.flatten }
  apply placementAround_exec placementBody _ tmp Hslot hplacementFit slotWidth hslotWidth reservoir calls hspec v M hplacement
    l hl hlen houterSrc _ (selectiveIdealPerm hK₀ active s R hs) _
  intro u
  obtain ⟨u₁, k, hu₁, hk, hx⟩ := temporaryProfilesClassifierMoved_exec ρ n m X rb scale active s
    body liveBody hlive outerBody houter activity hactivityHeader hactivityRow hactivityMask hactivityBadMask hactivityBadPhase hactivitySrc Lc hnfit w hwidth hQ hA hscale hn hR hB hrb hs (embDn e u) S
    data hempty hL hblank hfit hbank hdesc hinput hactivity hcount hscratch l hl hlen hsrc D hproject
    headerBody hheader Lrow Lwidth hRfit hwidthFit hrowInput hwidthInput hwork E hE
    widthBody hwidthBody Lr Lm hr hm hrowWidth hmaskWidth hwidthScratch hrow hmask
    classifierBody hclassifier F hF LK Ln Lo Lt hsegment hcountFit hoffset htop
    hsegmentInput hrunInput hcountInput hoffsetInput hphaseOffsetInput htopInput hclassifierScratch htemporary hphase forward
  have hp : embStk e M₀ = F₀ := by
    dsimp only [M₀, F₀]
    rw [embStk_update_stream e he, hM]
  change Exec classifierBody _ (mk (embDn e u) F₀) k
    (mk u₁ { F₀ with R := Function.update F₀.R (classifierCore (inactiveConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₀).flatten }) at hx
  rw [← hp] at hx
  obtain ⟨u₂, hu₂, hx₂⟩ := exec_emb_stream e he ι classifierBody placementBody hplacementBody _ u M₀ u₁ k
    (classifierCore (inactiveConfigurationCore repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l₀).flatten hx
  rw [embDn_user] at hu₁
  exact ⟨u₂, k, hu₂.trans hu₁, hk, hx₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing

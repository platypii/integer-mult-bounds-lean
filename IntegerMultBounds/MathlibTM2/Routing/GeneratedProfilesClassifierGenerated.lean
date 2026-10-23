module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveClassifierBank
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedProfilesWidthRepair

/-! Execute the full width/header/four-profile repair on the generated
classifier bank. All readiness follows from the initial mask-free configuration. -/

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

theorem generatedProfilesClassifierGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
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
    (v : HS inactiveProfileConfigurationT Q (prime + K) U) (S : Stacks T₀ (prime + K))
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
    (hmask : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))) = []) :
    let E₁ : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveConfigurationClassifierBank p₀ E.R }
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E₁ with R := inactiveProfileWidthBank rb (p₀).wy E₁.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairGeneratedProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileConfigurationT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * (p₀).wy + 11) + 2 * (p₀).wy + 6) + 1 : ℕ) +
        ((2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        (((3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits n + 1) + binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits n : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (4 * (2 * (n * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ)) + (2 * rb + 2 * (p₀).wy + 5 : ℕ) ∧
      Exec widthBody (.seq (binaryFieldBatch (fieldPairJobs (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))
          (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask))) Lr Lm rb (p₀).wy))
        (.seq (embProg (fieldCore (N := inactiveProfileHeaderT)) id (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq repairGeneratedProfilesProgram
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairGeneratedProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw)))))
          (metadataClean [fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row))),
            fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))])))
        (mk v E₁) steps
        (mk v' { E₁ with R := Function.update E₁.R (fieldCore (inactiveProfileHeaderRaw repairHost.src)) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let E₁ : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveConfigurationClassifierBank p₀ E.R }
  let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) E₁
  let S₁ := embStk sharedHeaderCore D₁
  have hDread (i : Fin inactiveProfileHeaderT) : E.R (fieldCore i) = D.R i := congrArg (fun C => C.R i) hE
  have hSread (i : Fin T₀) : D.R (sharedHeaderCore i) = S.R i := congrArg (fun C => C.R i) hproject
  have hraw (i : Fin repairT) (ht : i ≠ repairSetupSource (.inr .badMask)) (hp : i ≠ repairSetupSource (.inr .badPhase)) :
      S₁.R (e₀ (liveDescriptorCore i)) = S.R (e₀ (liveDescriptorCore i)) :=
    (inactiveConfigurationClassifierBank_core p₀ E.R i ht hp).trans ((hDread _).trans (hSread _))
  have haux (r : LiveDescriptorRole 11) : S₁.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [S₁, D₁, E₁, embStk, Function.comp_apply]
    exact (inactiveConfigurationClassifierBank_liveAux p₀ E.R r).trans ((hDread _).trans (hSread _))
  have hprofileAux (i : Fin 7) : S₁.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [S₁, D₁, E₁, embStk, Function.comp_apply]
    exact (inactiveConfigurationClassifierBank_profileAux p₀ E.R i).trans ((hDread _).trans (hSread _))
  have hheaderWork (r : HeaderWorkRole) : D₁.R (sharedHeaderWork r) = D.R (sharedHeaderWork r) := by
    dsimp only [D₁, E₁, embStk, Function.comp_apply]
    exact (inactiveConfigurationClassifierBank_headerWork p₀ E.R r).trans (hDread _)
  have hd : RepairPendingMaskData p₀ X rb wb wm wp wk R B (fun _ _ => [])
      (fun i => E.R (inactiveConfigurationCore i)) := by
    have hp : (fun i => E.R (inactiveConfigurationCore i)) = (fun i => S.R (e₀ (liveDescriptorCore i))) := by
      funext i
      exact (hDread _).trans (hSread _)
    rw [hp]
    exact data
  apply generatedProfilesWidthRepair_exec ρ n m X rb scale active s body liveBody hlive outerBody houter Lc hnfit w hwidth
    hQ hA hscale hn hR hB hrb hs v S₁
  · exact hd.inactiveConfigurationGenerated p₀ X rb
  · intro key
    exact (hraw _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm).trans (hempty key)
  · intro j
    exact (congrArg (fun C => C.L (sharedHeaderCore (e₀ (liveDescriptorCore j)))) hE).trans
      ((congrArg (fun C => C.L (e₀ (liveDescriptorCore j))) hproject).trans (hL j))
  · intro j hj
    exact (hraw j (repairBlank_extraSource j hj .badMask) (repairBlank_extraSource j hj .badPhase)).trans (hblank j hj)
  · exact hfit
  · intro r hr
    exact (haux r).trans (hbank r hr)
  · intro d
    exact (hraw _ (repairNonDescriptor_source (.inr .badMask) trivial d).symm
      (repairNonDescriptor_source (.inr .badPhase) trivial d).symm).trans (hdesc d)
  · intro j hj
    exact (haux (.input j)).trans (hinput j hj)
  · exact (hprofileAux 0).trans hcount
  · intro i hi
    exact (hprofileAux i).trans (hscratch i hi)
  · exact hl
  · exact hlen
  · exact (hraw repairHost.src (repairSetup_source_src (.inr .badMask)).symm
      (repairSetup_source_src (.inr .badPhase)).symm).trans hsrc
  · rfl
  · exact hheader
  · exact hRfit
  · exact hwidthFit
  · exact (hheaderWork (.binary 0)).trans hrowInput
  · exact (hheaderWork (.binary 1)).trans hwidthInput
  · intro r hr
    exact (hheaderWork r).trans (hwork r hr)
  · rfl
  · exact hwidthBody
  · exact hr
  · exact hm
  · have ha := inactiveConfigurationClassifierBank_widthAux p₀ E.R 0
    dsimp only [fieldAux] at ha
    dsimp only [E₁, fieldAux]
    exact ha.trans hrowWidth
  · have ha := inactiveConfigurationClassifierBank_widthAux p₀ E.R 1
    dsimp only [fieldAux] at ha
    dsimp only [E₁, fieldAux]
    exact ha.trans hmaskWidth
  · intro i hi
    have ha := inactiveConfigurationClassifierBank_widthAux p₀ E.R i
    dsimp only [fieldAux] at ha
    dsimp only [E₁, fieldAux]
    exact ha.trans (hwidthScratch i hi)
  · exact (inactiveConfigurationClassifierBank_row p₀ E.R).trans hrow
  · exact (inactiveConfigurationClassifierBank_keyMask p₀ E.R).trans hmask

end
end IntegerMultBounds.MathlibTM2.Routing

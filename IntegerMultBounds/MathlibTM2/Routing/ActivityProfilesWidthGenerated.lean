module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileWidths
public import IntegerMultBounds.MathlibTM2.Routing.ActivityProfilesHeaderRepair

/-! Execute generated-header and five-profile repair on the width-generated
bank, deriving readiness from the initial configuration with raw fields omitted. -/

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

theorem activityProfilesWidthGenerated_exec (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (activity : Fin repairT) (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (Lc : ℕ) (hnfit : n < 2 ^ Lc)
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveProfileHeaderT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p₀ X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairActivityProfileJobs, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j ∈ repairActivityProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
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
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D) :
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p₀).wy E.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p₀ X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairActivityProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        (((n * optionalAffineSourceIterationCost w.widthBits w.indexBits w.strideBits + 2 * n + 2 * (n * (w.indexBits + w.strideBits + 3)) + 16 * w.indexBits + 22) + ((3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits n + 1) + binaryAffineSourceGenerateCost Lc w.indexBits w.strideBits n) : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (5 * (2 * (n * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ) ∧
      Exec headerBody (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (repairActivityProfilesProgram activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairActivityProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw))))
        (mk v D₁) steps
        (mk v' { D₁ with R := Function.update D₁.R (inactiveProfileHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p₀).wy E.R }
  let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
  let S₁ := embStk sharedHeaderCore D₁
  have hDread (i : Fin inactiveProfileHeaderT) : E.R (fieldCore i) = D.R i := congrArg (fun C => C.R i) hE
  have hSread (i : Fin T₀) : D.R (sharedHeaderCore i) = S.R i := congrArg (fun C => C.R i) hproject
  have hraw (i : Fin repairT) (hr : i ≠ repairSetupSource (.inr .row)) (hm : i ≠ repairSetupSource (.inr .keyMask)) :
      S₁.R (e₀ (liveDescriptorCore i)) = S.R (e₀ (liveDescriptorCore i)) := by
    exact (inactiveProfileWidthBank_raw rb (p₀).wy E.R i hr hm).trans ((hDread _).trans (hSread _))
  have haux (r : LiveDescriptorRole 11) : S₁.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [S₁, D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_liveAux rb (p₀).wy E.R r).trans ((hDread _).trans (hSread _))
  have hprofileAux (i : Fin 7) : S₁.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [S₁, D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_profileAux rb (p₀).wy E.R i).trans ((hDread _).trans (hSread _))
  have hheaderWork (r : HeaderWorkRole) : D₁.R (sharedHeaderWork r) = D.R (sharedHeaderWork r) := by
    dsimp only [D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_headerWork rb (p₀).wy E.R r).trans (hDread _)
  have hdata : RepairPendingConfigurationData p₀ X rb wb wm wp wk R B (fun _ _ => [])
      (fun i => E.R (fieldCore (inactiveProfileHeaderRaw i))) := by
    have hp : (fun i => E.R (fieldCore (inactiveProfileHeaderRaw i))) = (fun i => S.R (e₀ (liveDescriptorCore i))) := by
      funext i
      exact (hDread _).trans (hSread _)
    rw [hp]
    exact data
  apply activityProfilesHeaderRepair_exec ρ n m X rb scale active s body liveBody hlive outerBody houter
    activity hactivityHeader Lc hnfit w hwidth hQ hA hscale hn hR hB hrb hs v S₁
  · exact hdata.inactiveProfileWidths p₀ X rb
  · intro key
    exact (hraw _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm).trans (hempty key)
  · intro j
    exact (congrArg (fun C => C.L (sharedHeaderCore (e₀ (liveDescriptorCore j)))) hE).trans
      ((congrArg (fun C => C.L (e₀ (liveDescriptorCore j))) hproject).trans (hL j))
  · intro j hj
    exact (hraw j (repairBlank_extraSource j hj .row) (repairBlank_extraSource j hj .keyMask)).trans (hblank j hj)
  · exact hfit
  · intro r hr
    exact (haux r).trans (hbank r hr)
  · intro d
    exact (hraw _ (repairNonDescriptor_source (.inr .row) trivial d).symm
      (repairNonDescriptor_source (.inr .keyMask) trivial d).symm).trans (hdesc d)
  · intro j hj
    exact (haux (.input j)).trans (hinput j hj)
  · exact (hraw activity hactivityRow hactivityMask).trans hactivity
  · exact (hprofileAux 0).trans hcount
  · intro i hi
    exact (hprofileAux i).trans (hscratch i hi)
  · exact hl
  · exact hlen
  · exact (hraw repairHost.src (repairSetup_source_src (.inr .row)).symm
      (repairSetup_source_src (.inr .keyMask)).symm).trans hsrc
  · rfl
  · exact hheader
  · exact hRfit
  · exact hwidthFit
  · exact (hheaderWork (.binary 0)).trans hrowInput
  · exact (hheaderWork (.binary 1)).trans hwidthInput
  · intro r hr
    exact (hheaderWork r).trans (hwork r hr)

end
end IntegerMultBounds.MathlibTM2.Routing

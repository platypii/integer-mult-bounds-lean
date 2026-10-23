module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileWidths
public import IntegerMultBounds.MathlibTM2.Routing.AllSourceProfilesHeaderRepair

/-! Execute generated-header and eleven-profile repair on the width-generated
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

theorem allSourceProfilesWidthGeneratedOfGeometry_exec
    (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (hguard : p.G + 1 < p.K) (scale : ℕ)
    (hscale : (0 : ℝ) < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (targets : Finset (Fin (p).wy)) (source : Fin (p).wy → Fin (p).wy)
    (hactive : active = profileActive p hK targets)
    (hsources : s = profileSources p hK targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc raw activity : Fin repairT) (hreg : [keySrc, raw, activity].Nodup)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hkeyRow : keySrc ≠ repairSetupSource (.inr .row))
    (hkeyMask : keySrc ≠ repairSetupSource (.inr .keyMask))
    (hrawRow : raw ≠ repairSetupSource (.inr .row))
    (hrawMask : raw ≠ repairSetupSource (.inr .keyMask))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p).K < 2 ^ w.strideBits) (hnfit : p.n < 2 ^ w.indexBits)
    (hwfit : (p).wy + 2 * (p).wc + X < 2 ^ w.coordinateBits)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS inactiveProfileHeaderT Q (prime + K) U) (S : Stacks T₀ (prime + K))
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B
      (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i))))
    (hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = [])
    (hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = [])
    (hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = [])
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p hK targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8)
    (hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten)
    (D : Stacks inactiveProfileHeaderT (prime + K)) (hproject : embStk sharedHeaderCore D = S)
    (headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U)
    (hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f))
    (Lrow Lwidth : ℕ) (hRfit : R < 2 ^ Lrow) (hwidthFit : (p).wc < 2 ^ Lwidth)
    (hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R)
    (hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p).wc)
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = [])
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D) :
    let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p).wy E.R }
    let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
    let H : Stacks inactiveProfileHeaderT (prime + K) := { D₁ with R := repairHeaderPairBank p X rb R B inactiveProfileHeaderBank D₁.R }
    let C₀ := embStk sharedHeaderCore H
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (2 * (14 * ((p).wc + (p).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        ((liveCoordinateProfilesCost p w : ℕ) +
        liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w C +
        (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p X rb R B : ℕ) ∧
      Exec headerBody (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw))))
        (mk v D₁) steps
        (mk v' { D₁ with R := Function.update D₁.R (inactiveProfileHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  let W : Stacks inactiveProfileConfigurationT (prime + K) := { E with R := inactiveProfileWidthBank rb (p).wy E.R }
  let D₁ := embStk (fieldCore (N := inactiveProfileHeaderT)) W
  let S₁ := embStk sharedHeaderCore D₁
  have hDread (i : Fin inactiveProfileHeaderT) : E.R (fieldCore i) = D.R i := congrArg (fun C => C.R i) hE
  have hSread (i : Fin T₀) : D.R (sharedHeaderCore i) = S.R i := congrArg (fun C => C.R i) hproject
  have hraw (i : Fin repairT) (hr : i ≠ repairSetupSource (.inr .row)) (hm : i ≠ repairSetupSource (.inr .keyMask)) :
      S₁.R (e₀ (liveDescriptorCore i)) = S.R (e₀ (liveDescriptorCore i)) := by
    exact (inactiveProfileWidthBank_raw rb (p).wy E.R i hr hm).trans ((hDread _).trans (hSread _))
  have haux (r : LiveDescriptorRole 11) : S₁.R (e₀ (liveDescriptorAux r)) = S.R (e₀ (liveDescriptorAux r)) := by
    dsimp only [S₁, D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_liveAux rb (p).wy E.R r).trans ((hDread _).trans (hSread _))
  have hprofileAux (i : Fin 7) : S₁.R (liveInactiveProfileAux i) = S.R (liveInactiveProfileAux i) := by
    dsimp only [S₁, D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_profileAux rb (p).wy E.R i).trans ((hDread _).trans (hSread _))
  have hheaderWork (r : HeaderWorkRole) : D₁.R (sharedHeaderWork r) = D.R (sharedHeaderWork r) := by
    dsimp only [D₁, W, embStk, Function.comp_apply]
    exact (inactiveProfileWidthBank_headerWork rb (p).wy E.R r).trans (hDread _)
  have hdata : RepairPendingConfigurationData p X rb wb wm wp wk R B (fun _ _ => [])
      (fun i => E.R (fieldCore (inactiveProfileHeaderRaw i))) := by
    have hp : (fun i => E.R (fieldCore (inactiveProfileHeaderRaw i))) = (fun i => S.R (e₀ (liveDescriptorCore i))) := by
      funext i
      exact (hDread _).trans (hSread _)
    rw [hp]
    exact data
  apply allSourceProfilesHeaderRepairOfGeometry_exec p X rb hG hK hguard scale hscale hn hradix hgap active s targets source hactive hsources body liveBody hlive outerBody houter
    keySrc raw activity hreg hkeyHeader hrawHeader hactivityHeader w hwidth hselectorWidthFit hkfit hnfit hwfit hQ hA hR hB hrb hs v S₁
  · exact hdata.inactiveProfileWidths p X rb
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
  · intro j
    exact (haux (.input j)).trans (hinput j)
  · exact (hraw keySrc hkeyRow hkeyMask).trans hkey
  · exact (hraw raw hrawRow hrawMask).trans hrawBlank
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


theorem allSourceProfilesWidthGenerated_exec
    (targets : Finset (Fin (p₀).wy)) (source : Fin (p₀).wy → Fin (p₀).wy)
    (hactive : active = profileActive p₀ hK₀ targets)
    (hsources : s = profileSources p₀ hK₀ targets source) (body : P → Pr P repairT Q (prime + K) U)
    (liveBody : P → Pr P repairLiveT Q (prime + K) U)
    (hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f))
    (outerBody : P → Pr P T₀ Q (prime + K) U)
    (houter : ∀ f, outerBody f = embProg e₀ id (liveBody f))
    (keySrc raw activity : Fin repairT) (hreg : [keySrc, raw, activity].Nodup)
    (hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k))
    (hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k))
    (hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k))
    (hkeyRow : keySrc ≠ repairSetupSource (.inr .row))
    (hkeyMask : keySrc ≠ repairSetupSource (.inr .keyMask))
    (hrawRow : raw ≠ repairSetupSource (.inr .row))
    (hrawMask : raw ≠ repairSetupSource (.inr .keyMask))
    (hactivityRow : activity ≠ repairSetupSource (.inr .row))
    (hactivityMask : activity ≠ repairSetupSource (.inr .keyMask))
    (w : LiveDescriptorWidths) (hwidth : w.selectorBits = w.coordinateBits)
    (hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits)
    (hkfit : (p₀).K < 2 ^ w.strideBits) (hnfit : n < 2 ^ w.indexBits)
    (hwfit : (p₀).wy + 2 * (p₀).wc + X < 2 ^ w.coordinateBits)
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
    (hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) →
      S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p₀ X hG₀ hK₀ active s repairLiveMode w r)
    (hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = [])
    (hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits
      (profileCoordinateInputs p₀ hK₀ targets source))
    (hrawBlank : S.R (liveZSourceActivity raw) = [])
    (hactivity : S.R (liveZSourceActivity activity) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits n)
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
    let G : Stacks T₀ (prime + K) := { C₀ with R := liveInactiveProfileBatchBank p₀ X hG₀ hK₀ active s repairLiveMode w C₀.R repairAllSourceProfileJobs }
    let C := embStk e₀ G
    ∃ (v' : HS inactiveProfileHeaderT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (2 * (14 * ((p₀).wc + (p₀).wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
        ((liveCoordinateProfilesCost p₀ w : ℕ) +
        liveRepairPrice p₀ X rb hG₀ hK₀ active s scale wb wm wp wk R B w C +
        (9 * (2 * (n * (w.selectorBits + 3)) + 2) + 2 * (2 * ((p₀).wc * (w.selectorBits + 3)) + 2) + 1 : ℕ)) + (repairHeaderErasePrice p₀ X rb R B : ℕ) ∧
      Exec headerBody (.seq (binaryRepairHeaderPairProgram sharedHeaderBinary inactiveProfileHeaderBank)
        (.seq (embProg sharedHeaderCore id (.seq (liveCoordinateProfilesProgram keySrc raw activity)
        (.seq (embProg e₀ id (liveRepairProgram hQ hA))
          (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)))))
          (metadataClean (embeddedGeneratedHeaderTargets inactiveProfileRaw))))
        (mk v D₁) steps
        (mk v' { D₁ with R := Function.update D₁.R (inactiveProfileHeaderRaw repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hp : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hnp : (n : ℝ) ≤ scale := by exact_mod_cast hn
  have hlog : (scale : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 scale := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale
  have hx := routingParameters_radices ρ n m (Nat.clog 2 scale) scale hp.le hlog
  exact allSourceProfilesWidthGeneratedOfGeometry_exec p₀ X rb hg.1 hg.2.1 hg.2.2
    scale hp hnp hx.1 hx.2 active s
    targets source hactive hsources body liveBody hlive outerBody houter keySrc raw activity
    hreg hkeyHeader hrawHeader hactivityHeader hkeyRow hkeyMask hrawRow hrawMask hactivityRow hactivityMask w hwidth
    hselectorWidthFit hkfit hnfit hwfit hQ hA hR hB hrb hs v S
    data hempty hL hblank hfit hbank hdesc hinput hkey hrawBlank hactivity hcount
    hscratch l hl hlen hsrc D hproject headerBody hheader Lrow Lwidth hRfit
    hwidthFit hrowInput hwidthInput hwork E hE

end
end IntegerMultBounds.MathlibTM2.Routing

module

public import IntegerMultBounds.MathlibTM2.Routing.JointBankAllSourceProfilesPriced
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedFixedProgram

/-! Pure data and readiness facts for a generated/placed call, packaged separately
from its actual execution theorem. No field contains an execution assertion. -/

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

structure GeneratedPlacedInput (t₀ Q K : ℕ) (P P' U : Type) where
  p : Par
  X : ℕ
  rb : ℕ
  hG : 0 < p.G
  hK : 0 < p.K
  hguard : p.G + 1 < p.K
  scale : ℕ
  hscale : (0 : ℝ) < scale
  hn : (p.n : ℝ) ≤ scale
  hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G
  hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)
  active : Fin p.n → Bool
  s : Fin p.n → SlotSource p X
  targets : Finset (Fin (p).wy)
  source : Fin (p).wy → Fin (p).wy
  hactive : active = profileActive p hK targets
  hsources : s = profileSources p hK targets source
  body : P → Pr P repairT Q (prime + K) U
  liveBody : P → Pr P repairLiveT Q (prime + K) U
  hlive : ∀ f, liveBody f = embProg liveDescriptorCore id (body f)
  outerBody : P → Pr P T₀ Q (prime + K) U
  houter : ∀ f, outerBody f = embProg e₀ id (liveBody f)
  keySrc : Fin repairT
  raw : Fin repairT
  activity : Fin repairT
  hreg : [keySrc, raw, activity].Nodup
  hkeyHeader : ∀ c k, keySrc ≠ repairRoutingConfig (.header c k)
  hrawHeader : ∀ c k, raw ≠ repairRoutingConfig (.header c k)
  hactivityHeader : ∀ c k, activity ≠ repairRoutingConfig (.header c k)
  hkeyRow : keySrc ≠ repairSetupSource (.inr .row)
  hkeyMask : keySrc ≠ repairSetupSource (.inr .keyMask)
  hrawRow : raw ≠ repairSetupSource (.inr .row)
  hrawMask : raw ≠ repairSetupSource (.inr .keyMask)
  hactivityRow : activity ≠ repairSetupSource (.inr .row)
  hactivityMask : activity ≠ repairSetupSource (.inr .keyMask)
  hkeyBadMask : keySrc ≠ repairSetupSource (.inr .badMask)
  hkeyBadPhase : keySrc ≠ repairSetupSource (.inr .badPhase)
  hrawBadMask : raw ≠ repairSetupSource (.inr .badMask)
  hrawBadPhase : raw ≠ repairSetupSource (.inr .badPhase)
  hactivityBadMask : activity ≠ repairSetupSource (.inr .badMask)
  hactivityBadPhase : activity ≠ repairSetupSource (.inr .badPhase)
  hkeySrc : keySrc ≠ repairHost.src
  hrawSrc : raw ≠ repairHost.src
  hactivitySrc : activity ≠ repairHost.src
  w : LiveDescriptorWidths
  hwidth : w.selectorBits = w.coordinateBits
  hselectorWidthFit : w.coordinateBits < 2 ^ w.widthBits
  hkfit : (p).K < 2 ^ w.strideBits
  hnfit : p.n < 2 ^ w.indexBits
  hwfit : (p).wy + 2 * (p).wc + X < 2 ^ w.coordinateBits
  hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q
  hA : 4 ≤ prime + K
  wb : ℕ
  wm : ℕ
  wp : ℕ
  wk : ℕ
  R : ℕ
  B : ℕ
  hR : 0 < R
  hB : 1 ≤ B
  hrb : R ≤ 2 ^ rb
  hs : ∀ c, (s c).Allowed active
  S : Stacks T₀ (prime + K)
  data : RepairPendingMaskData p X rb wb wm wp wk R B (fun _ _ => []) (fun i => S.R (e₀ (liveDescriptorCore i)))
  hempty : ∀ key, S.R (e₀ (liveDescriptorCore (repairSetupTarget key))) = []
  hL : ∀ j, S.L (e₀ (liveDescriptorCore j)) = []
  hblank : ∀ j, RepairBlank j → S.R (e₀ (liveDescriptorCore j)) = []
  hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j)
  hbank : ∀ r, (∀ j : Fin 11, r ≠ .input j) → S.R (e₀ (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r
  hdesc : ∀ d, S.R (e₀ (liveDescriptorCore (repairDescriptorSource d))) = []
  hinput : ∀ j, S.R (e₀ (liveDescriptorAux (.input j))) = []
  hkey : S.R (liveZSourceActivity keySrc) = sourceCoordinateInputWords w.indexBits w.strideBits (profileCoordinateInputs p hK targets source)
  hrawBlank : S.R (liveZSourceActivity raw) = []
  hactivity : S.R (liveZSourceActivity activity) = []
  hcount : S.R (liveInactiveProfileAux 0) = binSyms w.indexBits p.n
  hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []
  l : List (List (Fin (prime + K + 4)))
  hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X)
  hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8
  hsrc : S.R (e₀ (liveDescriptorCore repairHost.src)) = l.flatten
  D : Stacks inactiveProfileHeaderT (prime + K)
  hproject : embStk sharedHeaderCore D = S
  headerBody : P → Pr P inactiveProfileHeaderT Q (prime + K) U
  hheader : ∀ f, headerBody f = embProg sharedHeaderCore id (outerBody f)
  Lrow : ℕ
  Lwidth : ℕ
  hRfit : R < 2 ^ Lrow
  hwidthFit : (p).wc < 2 ^ Lwidth
  hrowInput : D.R (sharedHeaderBinary 0) = binSyms Lrow R
  hwidthInput : D.R (sharedHeaderBinary 1) = binSyms Lwidth (p).wc
  hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → D.R (sharedHeaderWork r) = []
  E : Stacks inactiveProfileConfigurationT (prime + K)
  hE : embStk (fieldCore (N := inactiveProfileHeaderT)) E = D
  widthBody : P → Pr P inactiveProfileConfigurationT Q (prime + K) U
  hwidthBody : ∀ f, widthBody f = embProg (fieldCore (N := inactiveProfileHeaderT)) id (headerBody f)
  Lr : ℕ
  Lm : ℕ
  hr : rb < 2 ^ Lr
  hm : (p).wy < 2 ^ Lm
  hrowWidth : E.R (fieldAux 0) = binSyms Lr rb
  hmaskWidth : E.R (fieldAux 1) = binSyms Lm (p).wy
  hwidthScratch : ∀ i : Fin 6, 2 ≤ i.val → E.R (fieldAux i) = []
  hrow : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .row)))) = []
  hmask : E.R (fieldCore (inactiveProfileHeaderRaw (repairSetupSource (.inr .keyMask)))) = []
  classifierBody : P → Pr P inactiveClassifierT Q (prime + K) U
  hclassifier : ∀ f, classifierBody f = embProg classifierCore id (widthBody f)
  F : Stacks inactiveClassifierT (prime + K)
  hF : embStk classifierCore F = E
  LK : ℕ
  Ln : ℕ
  Lo : ℕ
  Lt : ℕ
  hsegment : (p).K < 2 ^ LK
  hcountFit : p.n < 2 ^ Ln
  hoffset : p.ρ + 1 < 2 ^ Lo
  htop : p.m < 2 ^ Lt
  hsegmentInput : F.R (classifierAux 0) = binSyms LK (p).K
  hrunInput : F.R (classifierAux 1) = binSyms LK (p).G
  hcountInput : F.R (classifierAux 10) = binSyms Ln p.n
  hoffsetInput : F.R (classifierAux 13) = binSyms Lo (p.ρ + 1)
  hphaseOffsetInput : F.R (classifierAux 14) = binSyms Lo p.ρ
  htopInput : F.R (classifierAux 15) = binSyms Lt p.m
  hclassifierScratch : ∀ i : Fin 16, 2 ≤ i.val → i.val ≠ 10 → i.val < 13 → F.R (classifierAux i) = []
  htemporary : F.R (classifierCore inactiveClassifierTemporary) = []
  hphase : F.R (classifierCore inactiveClassifierPhase) = []
  ι : P → P'
  placementBody : P' → Pr P' (inactiveClassifierPlacementT t₀) Q (prime + K) U
  hplacementBody : ∀ f, placementBody (ι f) = embProg (inactiveClassifierPlacementEmbed (t₀ := t₀)) ι (classifierBody f)
  M : Stacks (inactiveClassifierPlacementT t₀) (prime + K)
  houterProject : embStk (inactiveClassifierPlacementEmbed (t₀ := t₀)) M = F
  Hslot : ℕ
  hplacementFit : 9 * Hslot ≤ fieldsLen (selectiveLen p X)
  slotWidth : ℕ
  hslotWidth : slotWidth ≤ Hslot
  reservoir : Fin 3
  hd : Fin 5 → Fin t₀
  pay : Fin t₀
  hhd : Function.Injective hd
  hpay : ∀ k, hd k ≠ pay
  hQplacement : swapStates hd pay hhd ≤ Q
  hT : swapT t₀ ≤ (inactiveClassifierPlacementT t₀)
  rowBits : List Bool
  Lcp : ℕ
  Lp : ℕ
  hwidthPlacement : fieldsLen (selectiveLen p X) < 2 ^ Lcp
  hBin : B < 2 ^ Lp
  hrowCanonical : GrowingCounterData.Canonical rowBits
  hrowNe : rowBits ≠ []
  hrowValue : Counter.value rowBits = R
  bankWords : Fin (swapT t₀) → List (Fin (prime + K + 4))
  hpay0 : bankWords (reg pay) = []
  hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → bankWords j = []
  hhdr0 : ∀ k, bankWords (reg (hd k)) = []
  hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ bankWords (reg i), x ≠ blank ∧ x.val < prime + 4
  hleft : ∀ j, M.L j = []
  hplacementBank : M.R = sharedScheduleInputBank (classifierCore (inactiveConfigurationCore repairHost.src)) F.R (reservoirExchangeSpecs (fieldsLen (selectiveLen p X)) Hslot hplacementFit slotWidth hslotWidth reservoir) bankWords Lcp Lp B rowBits l.flatten

theorem GeneratedPlacedInput.exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (v : HS TP₀ Q (prime + K) U) :
    let calls := binaryScheduleCalls slot₀ inactiveClassifierPlacementSlot_injective input.hd input.pay input.hhd input.hpay input.hQplacement input.hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir) input.hR input.hB input.rowBits input.Lcp input.Lp
      input.hwidthPlacement input.hBin input.hrowCanonical input.hrowNe input.hrowValue
    let forward := reservoirExchangeAction (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir input.R false
    let backward := reservoirExchangeAction (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir input.R true
    let l₀ := moveRecs forward input.l
    ∃ (v' : HS TP₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ allSourcePlacedRepairPrice input.p input.X input.rb input.hG input.hK input.active input.s
        input.scale input.wb input.wm input.wp input.wk input.R input.B input.Lrow input.Lwidth input.Lr input.Lm input.LK input.Ln input.Lo input.Lt input.w calls
        (reservoirExchangeOrder false) (reservoirExchangeOrder true) input.M input.E ∧
      Exec input.placementBody (allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA input.hd input.pay input.hhd input.hQplacement input.hT input.ι)
        (IntegerMultBounds.MathlibTM2.Host.mk v input.M) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { input.M with R := Function.update input.M.R (ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))) (moveRecs backward (moveRecs (selectiveIdealPerm input.hK input.active input.s input.R input.hs) l₀)).flatten }) := by
  have h := jointBankAllSourceProfilesPriced_exec
    input.p input.X input.rb input.hG input.hK input.hguard input.scale input.hscale input.hn input.hradix
    input.hgap input.active input.s input.targets input.source input.hactive input.hsources input.body input.liveBody input.hlive
    input.outerBody input.houter input.keySrc input.raw input.activity input.hreg input.hkeyHeader input.hrawHeader input.hactivityHeader input.hkeyRow
    input.hkeyMask input.hrawRow input.hrawMask input.hactivityRow input.hactivityMask input.hkeyBadMask input.hkeyBadPhase input.hrawBadMask input.hrawBadPhase input.hactivityBadMask
    input.hactivityBadPhase input.hkeySrc input.hrawSrc input.hactivitySrc input.w input.hwidth input.hselectorWidthFit input.hkfit input.hnfit input.hwfit
    input.hQ input.hA input.hR input.hB input.hrb input.hs v input.S input.data input.hempty
    input.hL input.hblank input.hfit input.hbank input.hdesc input.hinput input.hkey input.hrawBlank input.hactivity input.hcount
    input.hscratch input.l input.hl input.hlen input.hsrc input.D input.hproject input.headerBody input.hheader input.Lrow
    input.Lwidth input.hRfit input.hwidthFit input.hrowInput input.hwidthInput input.hwork input.E input.hE input.widthBody input.hwidthBody
    input.Lr input.Lm input.hr input.hm input.hrowWidth input.hmaskWidth input.hwidthScratch input.hrow input.hmask input.classifierBody
    input.hclassifier input.F input.hF input.LK input.Ln input.Lo input.Lt input.hsegment input.hcountFit input.hoffset
    input.htop input.hsegmentInput input.hrunInput input.hcountInput input.hoffsetInput input.hphaseOffsetInput input.htopInput input.hclassifierScratch input.htemporary input.hphase
    input.ι input.placementBody input.hplacementBody input.M input.houterProject input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir
    input.hd input.pay input.hhd input.hpay input.hQplacement input.hT input.rowBits input.Lcp input.Lp input.hwidthPlacement
    input.hBin input.hrowCanonical input.hrowNe input.hrowValue input.bankWords input.hpay0 input.hpriv input.hhdr0 input.hother input.hleft
    input.hplacementBank
  dsimp only at h
  rw [allSourcePlacedProgram_eq input.hd input.pay input.hhd input.hpay input.hQplacement input.hT
    (reservoirExchangeSpecs (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir)
    input.hR input.hB input.rowBits input.Lcp input.Lp input.hwidthPlacement input.hBin input.hrowCanonical input.hrowNe input.hrowValue
    input.keySrc input.raw input.activity input.hQ input.hA input.Lr input.Lm input.rb input.p.wy input.ι] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.Routing

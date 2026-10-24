module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveLive
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveHeaderFrame

/-! Named live-profile repair and generated-header programs, with fully charged
prices. Numerical parameters occur in prices and input contracts, not program code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def liveRepairPrice {K : ℕ} (scale wb wm wp wk R B : ℕ) (w : LiveDescriptorWidths)
    (S : Stacks repairLiveT (prime + K)) : ℝ :=
  let D : Stacks repairLiveT (prime + K) := { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let jobs := repairJobs p X rb wb wm wp wk R B
  let C := embStk liveDescriptorCore D
  let installed := metadataInstalled C.R jobs
  (liveDescriptorBatchCost p X hG hK active s repairLiveMode w repairLiveJobs : ℕ) +
    metadataInstallCost C.R jobs + repairDensityCoreCost p X rb R B scale { C with R := installed } +
    metadataCleanCost installed repairTargets + liveDescriptorEraseCost p X repairLiveMode repairLiveJobs

/-- Descriptor generation and actual installation derive the swap-bank price premise. -/
theorem liveRepairInstalledBank_length_le {K : ℕ} (wb wm wp wk R B width : ℕ)
    (S : Stacks repairLiveT (prime + K))
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (embStk liveDescriptorCore S).R)
    (hdesc : ∀ d, S.R (liveDescriptorCore (repairDescriptorSource d)) = [])
    (hleft : ∀ j, S.L (liveDescriptorCore j) = [])
    (hblank : ∀ j, RepairBlank j → S.R (liveDescriptorCore j) = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) (c : Fin 2) :
    let D : Stacks repairLiveT (prime + K) :=
      { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
    let C := embStk liveDescriptorCore D
    (∑ j, (metadataInstalled C.R (repairJobs p X rb wb wm wp wk R B) (repairHost.swaps c j)).length) ≤
      swapT 6 * (width + 1) := by
  let D : Stacks repairLiveT (prime + K) :=
    { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let C := embStk liveDescriptorCore D
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) C.R := data.liveGenerated p X rb hG hK active s hdesc
  exact repairSetup_swapBank_length_le p X rb hG hK active s C hd hleft
    (repairLiveBank_blank p X hG hK active s S.R hblank) width hheaders c

theorem liveRepairMetadataCleanCost_le {K : ℕ} (wb wm wp wk R B n width : ℕ)
    (S : Stacks repairLiveT (prime + K))
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (embStk liveDescriptorCore S).R)
    (hdesc : ∀ d, S.R (liveDescriptorCore (repairDescriptorSource d)) = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) :
    let D : Stacks repairLiveT (prime + K) :=
      { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
    let C := embStk liveDescriptorCore D
    metadataCleanCost (metadataInstalled C.R (repairJobs p X rb wb wm wp wk R B)) repairTargets ≤
      34 * (2 * (n * (n + 1) + (n + rb + B) + R * 2 ^ n + width + 2) + 2) + 1 := by
  let D : Stacks repairLiveT (prime + K) :=
    { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let C := embStk liveDescriptorCore D
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) C.R := data.liveGenerated p X rb hG hK active s hdesc
  exact repairMetadataCleanCost_le p X rb hG hK active s wb wm wp wk R B _ _ C.R hd
    (fun key => repairSetupPayload_length_le p X hG hK active s rb R B n width hfields
      (repairCanonicalHeaders p X rb R B) hheaders key)

theorem liveRepairMetadataInstallCost_le {K : ℕ} (wb wm wp wk R B n width : ℕ)
    (S : Stacks repairLiveT (prime + K))
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (embStk liveDescriptorCore S).R)
    (hdesc : ∀ d, S.R (liveDescriptorCore (repairDescriptorSource d)) = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) :
    let D : Stacks repairLiveT (prime + K) :=
      { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
    let C := embStk liveDescriptorCore D
    let wordBound := n * (n + 1) + n + rb + width + wb + wm + wp + wk + 1
    let widthBound := wb + wm + wp + wk
    let valueBound := n + rb + B + R * 2 ^ n
    metadataInstallCost C.R (repairJobs p X rb wb wm wp wk R B) ≤
      34 * (6 * wordBound + 7 + widthBound * (4 * valueBound + 11) + 2 * valueBound + 6) + 1 := by
  let D : Stacks repairLiveT (prime + K) :=
    { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let C := embStk liveDescriptorCore D
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) C.R := data.liveGenerated p X rb hG hK active s hdesc
  exact repairSetupInstallCost_le p X hG hK active s rb wb wm wp wk R B n width hfields
    (repairCanonicalHeaders p X rb R B) C.R hd hheaders

def liveRepairUniformOverhead (n rb R B width wb wm wp wk : ℕ) (w : LiveDescriptorWidths) : ℕ :=
  let wordBound := n * (n + 1) + n + rb + width + wb + wm + wp + wk + 1
  let widthBound := wb + wm + wp + wk
  let valueBound := n + rb + B + R * 2 ^ n
  (11 * (14 * w.coordinateBits + 16 + LiveDescriptorMode.uniformBackendBudget n n
    w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits) + 1) +
    (34 * (6 * wordBound + 7 + widthBound * (4 * valueBound + 11) + 2 * valueBound + 6) + 1) +
    (34 * (2 * (n * (n + 1) + (n + rb + B) + R * 2 ^ n + width + 2) + 2) + 1) +
    (11 * (2 * (n * (n + 1)) + 2) + 1)

theorem liveRepairUniformOverhead_mono (n rb R B : ℕ)
    {width width' wb wb' wm wm' wp wp' wk wk' : ℕ} {w w' : LiveDescriptorWidths}
    (hh : width ≤ width') (hb : wb ≤ wb') (hm : wm ≤ wm') (hp : wp ≤ wp') (hk : wk ≤ wk')
    (hi : w.indexBits ≤ w'.indexBits) (hg : w.groupBits ≤ w'.groupBits)
    (hs : w.strideBits ≤ w'.strideBits) (hsel : w.selectorBits ≤ w'.selectorBits)
    (hw : w.widthBits ≤ w'.widthBits) :
    liveRepairUniformOverhead n rb R B width wb wm wp wk w ≤
      liveRepairUniformOverhead n rb R B width' wb' wm' wp' wk' w' := by
  have hc : w.coordinateBits ≤ w'.coordinateBits := Nat.add_le_add hi hs
  have hd := LiveDescriptorMode.uniformBackendBudget_widths_mono n n hi hg hs hsel hw
  dsimp only [liveRepairUniformOverhead]
  gcongr

theorem liveRepairPrice_le {K : ℕ} (scale wb wm wp wk R B n width : ℕ)
    (w : LiveDescriptorWidths) (S : Stacks repairLiveT (prime + K))
    (hGK : p.G < p.K)
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (hn : p.n ≤ n) (hgroup : p.n * p.G ≤ n)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (embStk liveDescriptorCore S).R)
    (hdesc : ∀ d, S.R (liveDescriptorCore (repairDescriptorSource d)) = [])
    (hleft : ∀ j, S.L (liveDescriptorCore j) = [])
    (hblank : ∀ j, RepairBlank j → S.R (liveDescriptorCore j) = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) :
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w S ≤
      (liveRepairUniformOverhead n rb R B width wb wm wp wk w : ℕ) +
      (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℕ) +
      (12 * (selectiveUniformRotationCost n (R * 2 ^ n) (n + rb + B) : ℕ) +
        12 * selectiveUniformSwapCost repairT (R * 2 ^ n) (n + rb + B) p.wc
          (swapT 6 * (width + 1)) + 1) +
      repairUniformDensityScanCost n rb R B scale := by
  let D : Stacks repairLiveT (prime + K) :=
    { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let C := embStk liveDescriptorCore D
  let installed := metadataInstalled C.R (repairJobs p X rb wb wm wp wk R B)
  have hg := repairLiveBankCost_le p X hG hK active s hGK w n n hfields hn hgroup hfit
  have hi := liveRepairMetadataInstallCost_le p X rb hG hK active s wb wm wp wk R B n width
    S hfields data hdesc hheaders
  have hc := liveRepairMetadataCleanCost_le p X rb hG hK active s wb wm wp wk R B n width
    S hfields data hdesc hheaders
  have he : liveDescriptorEraseCost p X repairLiveMode repairLiveJobs ≤
      11 * (2 * (n * (n + 1)) + 2) + 1 := by
    simpa only [repairLiveJobs, List.length_ofFn] using
      liveDescriptorEraseCost_le p X repairLiveMode n hfields repairLiveJobs
  have hb := liveRepairInstalledBank_length_le p X rb hG hK active s wb wm wp wk R B width
    S data hdesc hleft hblank hheaders
  have hwy : p.wy ≤ n := (repairCompactRows_le_fields p X none).trans_eq hfields
  have hr := repairDensityCoreCost_le p X rb R B n (swapT 6 * (width + 1)) scale
    { C with R := installed } hfields hwy hb
  have hsum := add_le_add
    (add_le_add (add_le_add (add_le_add (Nat.cast_le.mpr hg) (Nat.cast_le.mpr hi)) hr)
      (Nat.cast_le.mpr hc)) (Nat.cast_le.mpr he)
  change liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w S ≤ _ at hsum
  refine hsum.trans_eq ?_
  simp only [liveRepairUniformOverhead, Nat.cast_add]
  ring

def liveRepairProgram {Q K : ℕ} {P U : Type}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairLiveT Q (prime + K) U :=
  .seq (liveDescriptorBatch repairLiveMode repairLiveJobs)
    (.seq (embProg liveDescriptorCore id (repairProgram hQ hA)) (metadataClean (repairLiveJobs.map LiveDescriptorJob.target)))

def liveHeaderRepairPrice {K : ℕ} (scale wb wm wp wk R B Lrow Lwidth : ℕ)
    (w : LiveDescriptorWidths) (S : Stacks repairLiveHeaderT (prime + K)) : ℝ :=
  let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank p X rb R B repairLiveHeaderBank S.R }
  (2 * (14 * (p.wc + p.wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w (embStk sharedHeaderCore G) +
    (repairHeaderErasePrice p X rb R B : ℕ)

def liveHeaderRepairProgram {Q K : ℕ} {P U : Type}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairLiveHeaderT Q (prime + K) U :=
  .seq (binaryRepairHeaderPairProgram sharedHeaderBinary repairLiveHeaderBank)
    (.seq (embProg sharedHeaderCore id (liveRepairProgram hQ hA))
      (metadataClean (embeddedGeneratedHeaderTargets (liveDescriptorCore (J := 11)))))

end
end IntegerMultBounds.MathlibTM2.Routing

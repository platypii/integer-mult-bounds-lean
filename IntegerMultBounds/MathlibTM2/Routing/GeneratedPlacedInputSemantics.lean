module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputTransport
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedPriceFrame
public import IntegerMultBounds.MathlibTM2.Routing.PlacedSelectiveBits

/-! Finite-rank semantics and a stream-independent price for actual generated/placed calls. -/

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

local notation "str₀" => ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))

def GeneratedPlacedInput.calls (input : GeneratedPlacedInput t₀ Q K P P' U) :=
  binaryScheduleCalls slot₀ inactiveClassifierPlacementSlot_injective input.hd input.pay input.hhd input.hpay input.hQplacement input.hT
      (reservoirExchangeSpecs (fieldsLen (selectiveLen input.p input.X)) input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir) input.hR input.hB input.rowBits input.Lcp input.Lp
      input.hwidthPlacement input.hBin input.hrowCanonical input.hrowNe input.hrowValue

theorem GeneratedPlacedInput.configurationRaw (input : GeneratedPlacedInput t₀ Q K P P' U)
    (j : Fin repairT) :
    input.E.R (inactiveConfigurationCore j) = input.S.R (inactiveProfileRaw j) := by
  have hw := congrArg (fun C => C.R (inactiveProfileHeaderRaw j)) input.hE
  have hh := congrArg (fun C => C.R (inactiveProfileRaw j)) input.hproject
  exact hw.trans hh

theorem GeneratedPlacedInput.configurationData (input : GeneratedPlacedInput t₀ Q K P P' U) :
    RepairPendingMaskData input.p input.X input.rb input.wb input.wm input.wp input.wk input.R input.B
      (fun _ _ => []) (fun j => input.E.R (inactiveConfigurationCore j)) :=
  input.data.congr input.p input.X input.rb (fun key => input.configurationRaw (repairSetupSource key))

theorem GeneratedPlacedInput.configurationBlank (input : GeneratedPlacedInput t₀ Q K P P' U)
    (j : Fin repairT) (hj : RepairBlank j) : input.E.R (inactiveConfigurationCore j) = [] :=
  (input.configurationRaw j).trans (input.hblank j hj)

def GeneratedPlacedInput.price (input : GeneratedPlacedInput t₀ Q K P P' U) : ℝ :=
  allSourcePlacedRepairPrice input.p input.X input.rb input.hG input.hK input.active input.s
        input.scale input.wb input.wm input.wp input.wk input.R input.B input.Lrow input.Lwidth input.Lr input.Lm input.LK input.Ln input.Lo input.Lt input.w input.calls
        (reservoirExchangeOrder false) (reservoirExchangeOrder true) input.M input.E

def GeneratedPlacedInput.generatedCostBound (input : GeneratedPlacedInput t₀ Q K P P' U)
    (n width : ℕ) : ℝ :=
  (allSourceGeneratedUniformOverhead input.p input.X input.rb n input.wb input.wm input.wp input.wk
    input.R input.B width input.Lrow input.Lwidth input.Lr input.Lm input.LK input.Ln input.Lo input.Lt input.w : ℕ) +
  (selectiveUniformKeyPassCost n input.rb (input.R * 2 ^ n) input.B : ℕ) +
  (12 * (selectiveUniformRotationCost n (input.R * 2 ^ n) (n + input.rb + input.B) : ℕ) +
    12 * selectiveUniformSwapCost repairT (input.R * 2 ^ n) (n + input.rb + input.B) input.p.wc
      (swapT 6 * (width + 1)) + 1) +
  repairUniformDensityScanCost n input.rb input.R input.B input.scale

theorem GeneratedPlacedInput.generatedPrice_le (input : GeneratedPlacedInput t₀ Q K P P' U)
    (n width : ℕ) (hfields : fieldsLen (selectiveLen input.p input.X) = n)
    (hn : input.p.n ≤ n) (hgroup : input.p.n * input.p.G ≤ n)
    (hheaders : ∀ c k, (repairCanonicalHeaders input.p input.X input.rb input.R input.B c k).length ≤ width) :
    allSourceGeneratedRepairPrice input.p input.X input.rb input.hG input.hK input.active input.s
      input.scale input.wb input.wm input.wp input.wk input.R input.B input.Lrow input.Lwidth
      input.Lr input.Lm input.LK input.Ln input.Lo input.Lt input.w input.E ≤
      input.generatedCostBound n width := by
  apply allSourceGeneratedRepairPrice_le input.p input.X input.rb input.hG input.hK input.active input.s
    input.scale input.wb input.wm input.wp input.wk input.R input.B width input.Lrow input.Lwidth
    input.Lr input.Lm input.LK input.Ln input.Lo input.Lt n input.w input.E
    (by have h := input.hguard; omega) hfields hn hgroup input.hfit (fun _ _ => []) input.configurationData
  · intro d
    exact (input.configurationRaw (repairDescriptorSource d)).trans (input.hdesc d)
  · intro j
    have hw := congrArg (fun C => C.L (inactiveProfileHeaderRaw j)) input.hE
    have hh := congrArg (fun C => C.L (inactiveProfileRaw j)) input.hproject
    exact (hw.trans hh).trans (input.hL j)
  · exact input.configurationBlank
  · exact hheaders

def GeneratedPlacedInput.placementCostBound (input : GeneratedPlacedInput t₀ Q K P P' U) : ℝ :=
  let n := fieldsLen (selectiveLen input.p input.X)
  (3 * swapConst * (TP₀ + 12 * swapT t₀ + 5 : ℕ) * (input.R * 2 ^ n * input.B : ℕ)) *
    (((max 1 (3 * input.Hslot) : ℕ) : ℝ) ^ Parameters.tau +
      2 * ((max 1 input.slotWidth : ℕ) : ℝ) ^ Parameters.tau) +
  3 * (generatedExchangeUniformOverhead t₀ TP₀ n input.R input.B input.Lp input.rowBits.length input.Lcp 0 +
    (3 * (input.Lcp * (4 * n + 31) + 2 * n + 26) + 10 * input.Lcp + 12) +
    (2 * n + 2 * input.Lcp + 9) : ℕ) + 1

theorem GeneratedPlacedInput.placementPrice_le (input : GeneratedPlacedInput t₀ Q K P P' U)
    (hbankWords : ∀ i, input.bankWords i = []) (reverse : Bool) :
    binaryExchangeChainCost input.calls input.M (reservoirExchangeOrder reverse) ≤ input.placementCostBound := by
  let n := fieldsLen (selectiveLen input.p input.X)
  let spec := reservoirExchangeSpecs n input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir
  have hstream : input.F.R (classifierCore (inactiveConfigurationCore repairHost.src)) = input.l.flatten :=
    (congrArg (fun C => C.R (inactiveConfigurationCore repairHost.src)) input.hF).trans
      ((input.configurationRaw repairHost.src).trans input.hsrc)
  have hbank (i : Fin (swapT t₀)) : input.M.R (slot₀ (.bank i)) = [] := by
    rw [input.hplacementBank]
    have hs := sharedScheduleInputBank_schedule (classifierCore (inactiveConfigurationCore repairHost.src))
      input.F.R spec input.bankWords input.Lcp input.Lp input.B input.rowBits input.l.flatten hstream (.bank i)
    exact hs.trans (hbankWords i)
  have hc := binaryScheduleChainCost_le slot₀ inactiveClassifierPlacementSlot_injective
    input.hd input.pay input.hhd input.hpay input.hQplacement input.hT spec input.hR input.hB
    input.rowBits input.Lcp input.Lp input.hwidthPlacement input.hBin input.hrowCanonical
    input.hrowNe input.hrowValue input.M hbank (reservoirExchangeOrder reverse)
  have hl : (reservoirExchangeOrder reverse).length = 3 := by cases reverse <;> rfl
  rw [hl] at hc
  have hs := reservoirExchangeWidthPower_sum_le n input.Hslot input.hplacementFit input.slotWidth
    input.hslotWidth input.reservoir reverse
  have hconst := swapConst_pos
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤
      3 * swapConst * (TP₀ + 12 * swapT t₀ + 5 : ℕ) * (input.R * 2 ^ n * input.B : ℕ) by positivity)
  exact hc.trans (add_le_add (add_le_add hm (le_refl _)) (le_refl _))

theorem GeneratedPlacedInput.price_le (input : GeneratedPlacedInput t₀ Q K P P' U)
    (n width : ℕ) (hfields : fieldsLen (selectiveLen input.p input.X) = n)
    (hn : input.p.n ≤ n) (hgroup : input.p.n * input.p.G ≤ n)
    (hbankWords : ∀ i, input.bankWords i = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders input.p input.X input.rb input.R input.B c k).length ≤ width) :
    input.price ≤ 2 * input.placementCostBound + input.generatedCostBound n width := by
  have hf := input.placementPrice_le hbankWords false
  have hb := input.placementPrice_le hbankWords true
  have hg := input.generatedPrice_le n width hfields hn hgroup hheaders
  change _ + _ + _ ≤ _
  have h := add_le_add (add_le_add hf hg) hb
  exact h.trans_eq (by ring)

def GeneratedPlacedInput.perm (input : GeneratedPlacedInput t₀ Q K P P' U) :=
  placedSelectivePerm input.hK input.active input.s input.hs
    (reservoirExchangeRank (fieldsLen (selectiveLen input.p input.X)) input.Hslot
      input.hplacementFit input.slotWidth input.hslotWidth input.reservoir input.R)

theorem GeneratedPlacedInput.perm_row (input : GeneratedPlacedInput t₀ Q K P P' U)
    (i : Fin (input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))) :
    (input.perm i).val / 2 ^ fieldsLen (selectiveLen input.p input.X) =
      i.val / 2 ^ fieldsLen (selectiveLen input.p input.X) :=
  placedSelectivePerm_row input.hK input.active input.s input.hs _
    (reservoirExchangeRank_row _ _ _ _ _ _ _) i

/-- The complete actual placed pipeline realizes one finite rank permutation. -/
theorem GeneratedPlacedInput.exec_perm (input : GeneratedPlacedInput t₀ Q K P P' U)
    (v : HS TP₀ Q (prime + K) U) :
    ∃ (v' : HS TP₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ input.price ∧
      Exec input.placementBody (allSourcePlacedFixedProgram input.keySrc input.raw input.activity
        input.hQ input.hA input.hd input.pay input.hhd input.hQplacement input.hT input.ι)
        (IntegerMultBounds.MathlibTM2.Host.mk v input.M) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { input.M with R := Function.update input.M.R str₀ (moveRecs input.perm input.l).flatten }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := input.exec v
  refine ⟨v', steps, hu, hm, ?_⟩
  dsimp only at he
  rw [reservoirPlacedSelective_records input.hK input.active input.s input.hs
    input.Hslot input.hplacementFit input.slotWidth input.hslotWidth input.reservoir input.l input.hl] at he
  exact he

/-- Every stage's complete price is independent of the current record values. -/
theorem GeneratedPlacedInput.replaceRecords_price (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8) :
    (input.replaceRecords l hl hlen).price = input.price := by
  have hblank : ∀ j, RepairBlank j → input.E.R (inactiveConfigurationCore j) = [] := by
    intro j hj
    have h := congrArg (fun S => S.R (inactiveProfileRaw j)) input.hproject
    have h' := congrArg (fun S => S.R (inactiveProfileHeaderRaw j)) input.hE
    exact h'.trans (h.trans (input.hblank j hj))
  dsimp only [GeneratedPlacedInput.price, GeneratedPlacedInput.calls, GeneratedPlacedInput.replaceRecords]
  exact allSourcePlacedRepairPrice_updateStream _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hblank

theorem GeneratedPlacedInput.withIO_price (input : GeneratedPlacedInput t₀ Q K P P' U)
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    (input.withIO inp out).price = input.price := by
  dsimp only [GeneratedPlacedInput.price, GeneratedPlacedInput.calls, GeneratedPlacedInput.withIO]
  rfl

/-- Run the actual core on the scheduler's current cursors and record stream. -/
theorem GeneratedPlacedInput.exec_on (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)
    (S : Stacks TP₀ (prime + K)) (hleft : ∀ j, S.L j = [])
    (hwords : S.R = Function.update input.M.R str₀ l.flatten)
    (v : HS TP₀ Q (prime + K) U) :
    ∃ (v' : HS TP₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ input.price ∧
      Exec input.placementBody (allSourcePlacedFixedProgram input.keySrc input.raw input.activity
        input.hQ input.hA input.hd input.pay input.hhd input.hQplacement input.hT input.ι)
        (IntegerMultBounds.MathlibTM2.Host.mk v S) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { S with R := Function.update S.R str₀ (moveRecs input.perm l).flatten }) := by
  let next := (input.replaceRecords l hl hlen).withIO S.inp S.out
  have hM : next.M = S := by
    apply Stacks.ext
    · rfl
    · rfl
    · exact funext (fun j => (input.hleft j).trans (hleft j).symm)
    · exact hwords.symm
  have hprice : next.price = input.price :=
    ((input.replaceRecords l hl hlen).withIO_price S.inp S.out).trans
      (input.replaceRecords_price l hl hlen)
  obtain ⟨v', steps, hu, hm, he⟩ := next.exec_perm v
  rw [hprice] at hm
  rw [hM] at he
  refine ⟨v', steps, hu, hm, ?_⟩
  simpa only [next, GeneratedPlacedInput.withIO, GeneratedPlacedInput.replaceRecords,
    GeneratedPlacedInput.perm] using he

end
end IntegerMultBounds.MathlibTM2.Routing

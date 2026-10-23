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

def GeneratedPlacedInput.price (input : GeneratedPlacedInput t₀ Q K P P' U) : ℝ :=
  allSourcePlacedRepairPrice input.p input.X input.rb input.hG input.hK input.active input.s
        input.scale input.wb input.wm input.wp input.wk input.R input.B input.Lrow input.Lwidth input.Lr input.Lm input.LK input.Ln input.Lo input.Lt input.w input.calls
        (reservoirExchangeOrder false) (reservoirExchangeOrder true) input.M input.E

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

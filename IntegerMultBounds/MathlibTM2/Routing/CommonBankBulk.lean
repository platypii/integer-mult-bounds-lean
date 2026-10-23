module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! The concrete bulk schedule executes on the common framed bank, preserving
all extra terminal registers and reusing the three outer loader tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen


def commonBankBulkProgram : Pr Empty (canonicalRouterCommonT + 3) Q (prime + K) Unit :=
  let r₀ : Fin (canonicalRouterStride n) := ⟨0, by
      have := canonicalRouterGap_pos n
      unfold canonicalRouterStride
      omega⟩
  let program : Pr Empty (originalMatchingScheduleT 6) Q (prime + K) Unit :=
      originalMatchingPlacedProgram (input r₀)
        (originalMatchingProducerEmbed (inactiveClassifierPlacementT 6))
        (originalMatchingRepairEmbed (inactiveClassifierPlacementT 6)) Empty.elim Empty.elim k reverse
  (embProg (framedCoreExtend canonicalRouterBulkT canonicalTerminalT) Empty.elim (delimitedScheduleProgram (framedCoreAux (originalMatchingScheduleT 6) 0)
          (framedCoreAux (originalMatchingScheduleT 6) 2)
          (framedCoreCallProgram (originalMatchingScheduleStream 6) canonicalRouterDelimiter
            (fun x => decide (x.val < 8)) Empty.elim program)))

def commonBankBulkPrice (stages : List (Fin (canonicalRouterStride n))) : ℝ :=
  delimitedSchedulePrice
        (fun r => originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages +
        (2 * (delimitedScheduleInput (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages).length + 3 : ℕ)

/-- Complete loop, table setup, framing and rewind overhead around the repair-price sum. -/
theorem commonBankBulkPrice_le (stages : List (Fin (canonicalRouterStride n))) :
    commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages ≤
      (stages.map (fun r => (input r).price)).sum +
      (stages.length * (canonicalRouterStageSetupBudget n R B + 2 +
        2 * canonicalRouterUniformFrameWidth n R B) + 4 : ℕ) := by
  let frame := fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
    (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter
  let price := fun r => originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
    (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter
  have hp := delimitedSchedulePrice_le price (fun r => (input r).price)
    (canonicalRouterStageSetupBudget n R B) stages
    (fun r _ => canonicalRouterStepPrice_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r)
  have hf := delimitedScheduleInput_length_le frame (canonicalRouterUniformFrameWidth n R B) stages
    (fun r _ => (canonicalRouterFrame_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).trans
      (canonicalRouterFrameWidth_uniform n hn R B hR hB r))
  have hr : ((2 * (delimitedScheduleInput frame stages).length + 3 : ℕ) : ℝ) ≤
      (2 * (stages.length * canonicalRouterUniformFrameWidth n R B) + 3 : ℕ) := by
    exact_mod_cast (show 2 * (delimitedScheduleInput frame stages).length + 3 ≤
      2 * (stages.length * canonicalRouterUniformFrameWidth n R B) + 3 by omega)
  change delimitedSchedulePrice price stages + (2 * (delimitedScheduleInput frame stages).length + 3 : ℕ) ≤ _
  generalize (stages.map (fun r => (input r).price)).sum = repairPrice at hp ⊢
  generalize delimitedSchedulePrice price stages = callPrice at hp ⊢
  generalize (delimitedScheduleInput frame stages).length = frameLength at hr ⊢
  generalize canonicalRouterStageSetupBudget n R B = C at hp ⊢
  generalize canonicalRouterUniformFrameWidth n R B = F at hr ⊢
  push_cast at hp hr ⊢
  nlinarith only [hp, hr]

theorem commonBankBulk_exec (stages : List (Fin (canonicalRouterStride n)))
    (v : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit)
    (S : Stacks (canonicalRouterCommonT + 3) (prime + K))
    (ready : FramedCoreReady (originalMatchingScheduleStream 6) (R * 2 ^ n) B
      (embStk (framedCoreExtend canonicalRouterBulkT canonicalTerminalT) S))
    (hinput : S.R (framedCoreAux canonicalRouterCommonT 0) = delimitedScheduleInput
      (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
        (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
        k mate canonicalRouterDelimiter) stages)
    (hsaved : S.R (framedCoreAux canonicalRouterCommonT 2) = []) :
    ∃ (v' : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit) (steps : ℕ),
      v'.user = v.user ∧
      (steps : ℝ) ≤ commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages ∧
      Exec (Empty.elim : Empty → Pr Empty (canonicalRouterCommonT + 3) Q (prime + K) Unit)
        (commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen) (mk v S) steps
        (mk v' { S with R := Function.update S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) (repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B (S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))))) }) := by
  dsimp only [commonBankBulkProgram, commonBankBulkPrice]
  let e := framedCoreExtend canonicalRouterBulkT canonicalTerminalT
  have hinput' : (embStk e S).R (framedCoreAux canonicalRouterBulkT 0) = S.R (framedCoreAux canonicalRouterCommonT 0) := by
    change S.R (e (framedCoreAux canonicalRouterBulkT 0)) = _
    dsimp only [e]
    rw [framedCoreExtend_aux]
  have hsaved' : (embStk e S).R (framedCoreAux canonicalRouterBulkT 2) = [] := by
    change S.R (e (framedCoreAux canonicalRouterBulkT 2)) = []
    dsimp only [e]
    rw [framedCoreExtend_aux]
    exact hsaved
  obtain ⟨u, steps, hu, hm, he⟩ := canonicalRouterBulk_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    stages (embDn e v) (embStk e S)
    ready (hinput'.trans hinput) hsaved'
  have hstr : (embStk e S).R (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6)) =
      S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) := by
    change S.R (e (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6))) = _
    dsimp only [e]
    rw [framedCoreExtend_core]
    rfl
  rw [hstr] at he
  obtain ⟨v', hv, hexec⟩ := exec_emb_stream e
    (framedCoreExtend_injective canonicalRouterBulkT canonicalTerminalT) Empty.elim
    Empty.elim Empty.elim (fun f => f.elim) _ v S u steps
    (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6)) _ he
  dsimp only [e] at hexec
  rw [framedCoreExtend_core] at hexec
  dsimp only [embDn] at hu
  refine ⟨v', steps, hv.trans hu, hm, ?_⟩
  exact hexec


/-- Any completed stream-only permutation, including terminal routing, leaves
the projected bulk bank ready without resetting terminal metadata. -/
theorem commonBankBulk_ready_update {A M B : ℕ}
    (S : Stacks (canonicalRouterCommonT + 3) A)
    (ready : FramedCoreReady (originalMatchingScheduleStream 6) M B
      (embStk (framedCoreExtend canonicalRouterBulkT canonicalTerminalT) S))
    (π : Equiv.Perm (Fin M)) :
    FramedCoreReady (originalMatchingScheduleStream 6) M B
      (embStk (framedCoreExtend canonicalRouterBulkT canonicalTerminalT)
        { S with R := Function.update S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) (repairStreamEffect π B (S.R (framedCoreEmbed canonicalRouterCommonT
            (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))))) }) := by
  let e := framedCoreExtend canonicalRouterBulkT canonicalTerminalT
  have hmap : e (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6)) =
      framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) := by
    dsimp only [e]
    rw [framedCoreExtend_core]
    rfl
  have h := FramedCoreReady.updateStream (originalMatchingScheduleStream 6) (embStk e S) ready π
  rw [← embStk_update_stream e (framedCoreExtend_injective canonicalRouterBulkT canonicalTerminalT)] at h
  have hread : (embStk e S).R (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6)) =
      S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) := by
    change S.R (e (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6))) = _
    rw [hmap]
  rw [hmap, hread] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.Routing

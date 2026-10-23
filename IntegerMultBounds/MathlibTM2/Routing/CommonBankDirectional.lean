module

public import IntegerMultBounds.MathlibTM2.Routing.CommonBankBulk
public import IntegerMultBounds.MathlibTM2.Routing.CommonBankTerminal

/-! Actual terminal-then-bulk execution on one framed bank. Both phases restore
all metadata and workspace; their only shared effect is the live record stream. -/

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


def canonicalRouterDirectionalPerm (stages : List (Fin (canonicalRouterStride n))) :
    Equiv.Perm (Fin (R * 2 ^ n)) :=
  (canonicalRouterTerminalPerm n hn mate hinv k reverse R).trans
    (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages)

theorem canonicalRouterDirectional_records (stages : List (Fin (canonicalRouterStride n))) :
    repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B
      (moveRecs (canonicalRouterTerminalPerm n hn mate hinv k reverse R) l).flatten =
    (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten := by
  have hshape : ∀ row ∈ moveRecs (canonicalRouterTerminalPerm n hn mate hinv k reverse R) l,
      row.length = B := by
    intro row hr
    exact (hlen row (mem_moveRecs _ hl hr)).1
  calc
    _ = (moveRecs (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages)
        (moveRecs (canonicalRouterTerminalPerm n hn mate hinv k reverse R) l)).flatten :=
      (flatten_moveRecs _ _ hshape).symm
    _ = _ := congrArg List.flatten (moveRecs_trans _ _ l hl).symm

theorem canonicalRouterDirectionalPerm_bits (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
      (List.finRange (canonicalRouterStride n)) i).val.testBit q.val) =
    shear ((matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse).image
      (canonicalRouterMiddleEmbedding n hn k))
      (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k) (fun q => i.val.testBit q.val) := by
  have hb := canonicalRouterSchedulePerm_bulk_bits n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    (canonicalRouterTerminalPerm n hn mate hinv k reverse R i)
  have ht := elementaryRankSchedule_shear R _ _ (canonicalRouterTerminal_source n hn mate hinv k reverse) i
  change (fun q : Fin n => (canonicalRouterTerminalPerm n hn mate hinv k reverse R i).val.testBit q.val) = _ at ht
  rw [ht] at hb
  exact hb.trans (canonicalRouter_bulk_terminal_shear n hn mate hinv k reverse _)

theorem commonBankDirectional_exec
    (L Lb : ℕ) (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (stages : List (Fin (canonicalRouterStride n)))
    (v : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit)
    (S : Stacks (canonicalRouterCommonT + 3) (prime + K))
    (hleft : ∀ j, S.L (canonicalRouterTerminalLift 3 j) = [])
    (hbank : ∀ j, S.R (canonicalRouterTerminalLift 3 j) =
      canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
        (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L
          (canonicalRouterTerminalCoordinates n hn mate hinv k reverse)) n L Lb B rowBits j)
    (ready : FramedCoreReady (originalMatchingScheduleStream 6) (R * 2 ^ n) B
      (embStk (framedCoreExtend canonicalRouterBulkT canonicalTerminalT) S))
    (hinput : S.R (framedCoreAux canonicalRouterCommonT 0) = delimitedScheduleInput
      (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
        (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
        k mate canonicalRouterDelimiter) stages)
    (hsaved : S.R (framedCoreAux canonicalRouterCommonT 2) = []) :
    ∃ (v' : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalTerminalPrice n R B L Lb rowBits.length
        (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).length +
        commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages ∧
      Exec Empty.elim (.seq
        (embProg (canonicalRouterTerminalLift 3) Empty.elim (canonicalTerminalProgram hQ n R B Lb rowBits.length))
        (commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen))
        (mk v S) steps (mk v' { S with R := Function.update S.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten }) := by
  let str := framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))
  let π := canonicalRouterTerminalPerm n hn mate hinv k reverse R
  let output := (moveRecs π l).flatten
  let S₁ : Stacks (canonicalRouterCommonT + 3) (prime + K) := { S with R := Function.update S.R str output }
  have hstream : S.R str = l.flatten := by
    have h := hbank (canonicalTerminalRouter .str)
    rw [canonicalRouterTerminalLift_stream] at h
    simpa only [canonicalTerminalBank_fixed_router, ite_true, str, framedCoreEmbed] using h
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := commonBankTerminal_exec 3 Empty.elim Empty.elim Empty.elim
    (fun f => f.elim) n R B L Lb hn mate hinv k reverse hn0 hnfit hBfit hnB hR hB
    rowBits hrow hrowNe hrowValue hQ v S hleft l hl (fun r hr => (hlen r hr).1)
    (fun r hr => (hlen r hr).2) hbank
  have hready₁ := commonBankBulk_ready_update S ready π
  have hout : repairStreamEffect π B l.flatten = output :=
    (flatten_moveRecs π l (fun r hr => (hlen r hr).1)).symm
  rw [hstream, hout] at hready₁
  have hinput₁ : S₁.R (framedCoreAux canonicalRouterCommonT 0) = S.R (framedCoreAux canonicalRouterCommonT 0) := by
    dsimp only [S₁, str]
    rw [Function.update_of_ne (framedCoreEmbed_aux canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) 0).symm]
  have hsaved₁ : S₁.R (framedCoreAux canonicalRouterCommonT 2) = [] := by
    dsimp only [S₁, str]
    rw [Function.update_of_ne (framedCoreEmbed_aux canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) 2).symm]
    exact hsaved
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := commonBankBulk_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages v₁ S₁ hready₁ (hinput₁.trans hinput) hsaved₁
  dsimp only [S₁] at he₂
  rw [Function.update_self, Function.update_idem] at he₂
  rw [canonicalRouterDirectional_records n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages] at he₂
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  simp only [Nat.cast_add]
  exact add_le_add hm₁ hm₂

end
end IntegerMultBounds.MathlibTM2.Routing

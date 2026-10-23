module

public import IntegerMultBounds.MathlibTM2.Routing.CommonBankDirectional

/-! Concrete inner directional bank: blank bulk workspace, installed terminal
metadata and the actual framed residue input on the shared loader source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
theorem delimitedBankFrames_small {T A bound : ℕ} (delimiter : Fin (A + 4))
    (hd : delimiter.val < bound) (jobs : List (Fin T × List (Fin (A + 4))))
    (hw : ∀ job ∈ jobs, ∀ x ∈ job.2, x.val < bound) :
    ∀ x ∈ delimitedBankFrames delimiter jobs, x.val < bound := by
  induction jobs with
  | nil => simp [delimitedBankFrames]
  | cons job jobs ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw job (by simp) x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hd
      · exact ih (fun j hj => hw j (by simp [hj])) x hx

theorem extend_words_small {α β : Type*} {A bound : ℕ} (e : α → β)
    (he : Function.Injective e) (words : α → List (Fin (A + 4)))
    (fallback : β → List (Fin (A + 4)))
    (hw : ∀ j x, x ∈ words j → x.val < bound)
    (hf : ∀ j x, x ∈ fallback j → x.val < bound) :
    ∀ j x, x ∈ Function.extend e words fallback j → x.val < bound := by
  intro j x hx
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [he.extend_apply] at hx
    exact hw i x hx
  · rw [Function.extend_apply' _ _ _ hj] at hx
    exact hf j x hx

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (L Lb : ℕ) (rowBits : List Bool) (stages : List (Fin (canonicalRouterStride n)))

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen

def canonicalDirectionalBulkInput : List (Fin (prime + K + 4)) :=
  delimitedScheduleInput (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
    (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    k mate canonicalRouterDelimiter) stages

/-- The complete nested bulk input is bounded by the sum of residue budgets. -/
theorem canonicalDirectionalBulkInput_length_le :
    (canonicalDirectionalBulkInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages).length ≤
      (stages.map (canonicalRouterFrameWidth n R B hR hB)).sum := by
  unfold canonicalDirectionalBulkInput
  induction stages with
  | nil => simp [delimitedScheduleInput]
  | cons r stages ih =>
    simp only [delimitedScheduleInput, List.length_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add
      (canonicalRouterFrame_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r) ih

theorem canonicalDirectionalBulkInput_small : ∀ x ∈ canonicalDirectionalBulkInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages, x.val < 9 := by
  unfold canonicalDirectionalBulkInput
  induction stages with
  | nil => simp [delimitedScheduleInput]
  | cons r stages ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · apply delimitedBankFrames_small canonicalRouterDelimiter (by change (8 : ℕ) < 9; decide) _ ?_ x hx
      intro job hj y hy
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
      exact (canonicalRouterStage_words n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j y hy).trans (by decide)
    · exact ih x hx

local notation "terminal" => canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
  (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L
    (canonicalRouterTerminalCoordinates n hn mate hinv k reverse)) n L Lb B rowBits

local notation "bulk" => Function.update (fun _ : Fin canonicalRouterBulkT => ([] : List (Fin (prime + K + 4))))
  (originalMatchingScheduleStream 6) l.flatten

local notation "source" => canonicalDirectionalBulkInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages

/-- All installed data are explicit words; this constructor performs no execution. -/
def canonicalDirectionalBank : Fin (canonicalRouterCommonT + 3) → List (Fin (prime + K + 4)) :=
  Function.extend (framedCoreEmbed canonicalRouterCommonT) (canonicalRouterCommonBank bulk terminal)
    (fun j => if j = framedCoreAux canonicalRouterCommonT 0 then source else [])

local notation "bank" => canonicalDirectionalBank n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages

theorem canonicalDirectionalBank_core (j : Fin canonicalRouterCommonT) :
    bank (framedCoreEmbed canonicalRouterCommonT j) = canonicalRouterCommonBank bulk terminal j :=
  (framedCoreEmbed_injective canonicalRouterCommonT).extend_apply _ _ j

theorem canonicalDirectionalBank_aux (j : Fin 3) :
    bank (framedCoreAux canonicalRouterCommonT j) = if j = 0 then source else [] := by
  unfold canonicalDirectionalBank
  rw [Function.extend_apply']
  · by_cases hj : j = 0
    · subst j; simp only [ite_true]
    · rw [ite_eq_right ((framedCoreAux_injective canonicalRouterCommonT).ne hj), ite_eq_right hj]
  · rintro ⟨i, hi⟩
    exact framedCoreEmbed_aux canonicalRouterCommonT i j hi

theorem canonicalDirectionalBank_terminal (j : Fin canonicalTerminalT) :
    bank (canonicalRouterTerminalLift 3 j) = terminal j := by
  rw [show canonicalRouterTerminalLift 3 j =
    framedCoreEmbed canonicalRouterCommonT (canonicalRouterTerminalEmbed j) from rfl,
    canonicalDirectionalBank_core]
  apply canonicalRouterCommonBank_terminal
  simp only [Function.update_self, canonicalTerminalBank_fixed_router, ite_true]

theorem canonicalDirectionalBank_stream :
    bank (framedCoreEmbed canonicalRouterCommonT
      (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) = l.flatten := by
  rw [canonicalDirectionalBank_core, canonicalRouterCommonBank_bulk, Function.update_self]

/-- Every outer-loader word is bounded without reference to matching or payload values. -/
theorem canonicalDirectionalBank_length_le (j : Fin (canonicalRouterCommonT + 3))
    (hj : j ≠ framedCoreEmbed canonicalRouterCommonT
      (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) :
    (bank j).length ≤ L + Lb + rowBits.length +
      (131 * canonicalRouterGap n) * (2 * L + 2) +
      (stages.map (canonicalRouterFrameWidth n R B hR hB)).sum := by
  have ht : ∀ i, i ≠ canonicalTerminalRouter .str →
      (terminal i).length ≤ L + Lb + rowBits.length + (131 * canonicalRouterGap n) * (2 * L + 2) := by
    intro i hi
    have hword := canonicalTerminalRoutingBank_length_le l.flatten
      (elementaryCoordinateFrames L (canonicalRouterTerminalCoordinates n hn mate hinv k reverse))
      n L Lb B rowBits i hi
    have hframe := canonicalRouterTerminalFrames_length_le (A := prime + K) n hn mate hinv k reverse L
    omega
  by_cases hc : ∃ i, framedCoreEmbed canonicalRouterCommonT i = j
  · obtain ⟨i, rfl⟩ := hc
    rw [canonicalDirectionalBank_core]
    have hi : i ≠ canonicalRouterBulkEmbed (originalMatchingScheduleStream 6) := by
      intro he
      exact hj (congrArg (framedCoreEmbed canonicalRouterCommonT) he)
    have hb : ∀ q, q ≠ originalMatchingScheduleStream 6 → (bulk q).length ≤ 0 := by
      intro q hq
      rw [Function.update_of_ne hq]
      exact Nat.le_refl _
    have hword := canonicalRouterCommonBank_length_le bulk terminal 0 _ hb ht i hi
    omega
  · unfold canonicalDirectionalBank
    rw [Function.extend_apply' _ _ _ hc]
    split
    · have hs := canonicalDirectionalBulkInput_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages
      omega
    · exact Nat.zero_le _

theorem canonicalDirectionalBank_ready (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    FramedCoreReady (originalMatchingScheduleStream 6) (R * 2 ^ n) B
      (embStk (framedCoreExtend canonicalRouterBulkT canonicalTerminalT)
        (⟨inp, out, fun _ => [], bank⟩ : Stacks (canonicalRouterCommonT + 3) (prime + K))) := by
  constructor
  · intro j; rfl
  · intro j hj
    change bank (framedCoreExtend canonicalRouterBulkT canonicalTerminalT
      (framedCoreEmbed canonicalRouterBulkT j)) = []
    rw [framedCoreExtend_core, canonicalDirectionalBank_core]
    change canonicalRouterCommonBank bulk terminal (canonicalRouterBulkEmbed j) = []
    rw [canonicalRouterCommonBank_bulk, Function.update_of_ne hj]
  · change bank (framedCoreExtend canonicalRouterBulkT canonicalTerminalT
      (framedCoreAux canonicalRouterBulkT 1)) = []
    rw [framedCoreExtend_aux, canonicalDirectionalBank_aux]
    rfl
  · refine ⟨l, hl, hlen, ?_⟩
    change bank (framedCoreExtend canonicalRouterBulkT canonicalTerminalT
      (framedCoreEmbed canonicalRouterBulkT (originalMatchingScheduleStream 6))) = _
    rw [framedCoreExtend_core, canonicalDirectionalBank_core]
    change canonicalRouterCommonBank bulk terminal
      (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) = _
    rw [canonicalRouterCommonBank_bulk, Function.update_self]

theorem canonicalDirectionalBank_small : ∀ j x, x ∈ bank j → x.val < 9 := by
  unfold canonicalDirectionalBank canonicalRouterCommonBank
  apply extend_words_small _ (framedCoreEmbed_injective canonicalRouterCommonT)
  · apply extend_words_small _ canonicalRouterBulkEmbed_injective
    · intro j x hx
      by_cases hj : j = originalMatchingScheduleStream 6
      · subst j
        rw [Function.update_self] at hx
        obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx
        exact ((hlen row hr).2 x hx).trans (by decide)
      · rw [Function.update_of_ne hj] at hx
        exact (List.not_mem_nil hx).elim
    · apply extend_words_small _ canonicalRouterTerminalEmbed_injective
      · intro j x hx
        exact (canonicalTerminalRoutingBank_small l.flatten
          (by intro x hx; obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx; exact (hlen row hr).2 x hx)
          n L Lb B rowBits (canonicalRouterTerminalCoordinates n hn mate hinv k reverse) j x hx).trans (by decide)
      · intro j x hx; exact (List.not_mem_nil hx).elim
  · intro j x hx
    split at hx
    · exact canonicalDirectionalBulkInput_small n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages x hx
    · exact (List.not_mem_nil hx).elim

/-- Execute the concrete installed bank without caller-supplied readiness or
terminal projection assumptions. Installation itself is charged by the outer frame. -/
theorem canonicalDirectionalBank_exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit) :
    let C : Stacks (canonicalRouterCommonT + 3) (prime + K) := ⟨inp, out, fun _ => [], bank⟩
    ∃ (v' : HS (canonicalRouterCommonT + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalTerminalPrice n R B L Lb rowBits.length
        (canonicalRouterTerminalCoordinates n hn mate hinv k reverse).length +
        commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages ∧
      Exec Empty.elim (.seq
        (embProg (canonicalRouterTerminalLift 3) Empty.elim (canonicalTerminalProgram hQ n R B Lb rowBits.length))
        (commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen))
        (mk v C) steps (mk v' { C with R := Function.update C.R (framedCoreEmbed canonicalRouterCommonT (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) (moveRecs (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) l).flatten }) := by
  apply commonBankDirectional_exec n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
    L Lb hn0 hnfit hBfit hnB rowBits hrow hrowNe hrowValue stages v _ (fun _ => rfl)
    (canonicalDirectionalBank_terminal n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages)
    (canonicalDirectionalBank_ready n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages inp out)
  · exact canonicalDirectionalBank_aux n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages 0
  · exact canonicalDirectionalBank_aux n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages 2

end
end IntegerMultBounds.MathlibTM2.Routing

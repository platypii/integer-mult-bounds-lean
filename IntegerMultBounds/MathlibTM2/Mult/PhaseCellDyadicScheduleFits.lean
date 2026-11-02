module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicSelector
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Metadata fit follows from the selector's exact output contract and the
bounded-variable invariant of the table machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem selectDyadicStage_values_lt (a b C W i : ℕ) (hbits : a+b < W)
    (hfit : C*2^(a+b) < 2^W) (hi : i < dyadicStageCount (a+b) a b) :
    ∀ x ∈ List.ofFn (selectDyadicStage (a+b) a b C (dyadicStageCount (a+b) a b) i).values,
      x < 2^W := by
  let N := dyadicStageCount (a+b) a b
  let st : TblSt 16 4 := ⟨fun j => if j = 3 then N else if j = 4 then C else
    if j = 6 then a else if j = 7 then b else if j = 15 then i else 0,[]⟩
  have hN : N ≤ a+b := dyadicStageCount_le (a+b) a b (by omega)
  have hwide : a+b < 2^W := hbits.trans Nat.lt_two_pow_self
  have hseed : C < 2^W := (Nat.le_mul_of_pos_right C (Nat.two_pow_pos _)).trans_lt hfit
  have hbound : ∀ j, st.val j < 2^W := by
    intro j
    dsimp only [st]
    split_ifs <;> omega
  obtain ⟨F,k,hrun,hpost,hcost⟩ := generatedDyadicSelectorCode_do (W := W) (w := W) st
    (by simp [st]) (by simp [st]) (by simp [st]) (by simp [st,N]) (by simp [st]) hbits hfit hi
  have hF := hrun.bounded hbound
  rcases hpost with ⟨h11,h9,h10,h5,h2,h14,hacc,hframe⟩
  intro x hx
  simp only [DyadicStageRow.values_list,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [←h11]; exact hF 11
  · rw [←h14]; exact hF 14
  · rw [←h9]; exact hF 9
  · rw [←h10]; exact hF 10
  · rw [←h10]; exact hF 10

theorem dyadicScheduleValues_lt (a b C W : ℕ) (hbits : a+b < W)
    (hfit : C*2^(a+b) < 2^W) :
    ∀ x ∈ dyadicScheduleValues (a+b) a b C, x < 2^W := by
  intro x hx
  simp only [dyadicScheduleValues,dyadicSelectedRows,List.mem_flatMap,List.mem_map] at hx
  obtain ⟨row,⟨i,hi,rfl⟩,hx⟩ := hx
  exact selectDyadicStage_values_lt a b C W i hbits hfit (List.mem_range.mp hi) x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

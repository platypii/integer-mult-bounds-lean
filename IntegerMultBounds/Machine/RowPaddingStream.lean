import IntegerMultBounds.Machine.RowPaddingBlock
import Mathlib.Data.List.Flatten

/-! Literal counted streaming padding across all consumed groups. The two
reusable clocks are supplied with retained sentinels; initialization, origin
restoration and final sentinel deletion belong to the enclosing wrapper. -/
namespace IntegerMultBounds.Machine.RowPaddingStream
open CountedRawFill (filled)

def consumed (groups : List (List (Fin 4))) (i : ℕ) := (groups.take i).flatten
def padded (groups : List (List (Fin 4))) (m : ℕ) :=
  groups.map (fun xs => xs ++ List.replicate m (bitSymbol false))

theorem consumed_step (groups : List (List (Fin 4))) (i : ℕ) (hi : i < groups.length) :
    consumed groups (i+1) = consumed groups i ++ groups[i] := by
  change (groups.take (i+1)).flatten = (groups.take i).flatten ++ groups[i]
  rw [List.take_succ_eq_append_getElem hi]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]

theorem current_view (source : ℤ → Fin 4) (p : ℤ) (groups : List (List (Fin 4)))
    (i : ℕ) (hi : i < groups.length) :
    putWord (filled (putWord source p groups.flatten) p (consumed groups i).length blank)
      (p+(consumed groups i).length) groups[i] =
      filled (putWord source p groups.flatten) p (consumed groups i).length blank := by
  apply WordSegments.of_agrees
  intro j hj
  rw [CountedRawFill.filled_outside _ _ _ _ _ (Or.inr (by omega))]
  have hd : groups.flatten = consumed groups i ++ groups[i] ++ (groups.drop (i+1)).flatten := by
    have hh := congrArg List.flatten (List.take_append_drop (i+1) groups)
    rw [List.flatten_append] at hh
    change consumed groups (i+1) ++ (groups.drop (i+1)).flatten = groups.flatten at hh
    rw [consumed_step groups i hi] at hh
    exact hh.symm
  rw [hd]
  have hm := congrFun (WordSegments.middle source p (consumed groups i) groups[i]
    (groups.drop (i+1)).flatten) (p+(consumed groups i).length+j)
  rw [WordSegments.get _ _ _ j hj] at hm
  exact hm.symm

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) : Tapes 7 0 :=
  CountedLoopReuse.bank (RowPaddingBlock.bank source dest p q valid padding)
    CountedCopyReuse.empty (CountedCopyReuse.binary count) 1 1

def program : Program 7 (7+(36+5)+4) 0 := CountedLoopReuse.program RowPaddingBlock.program

def state (source dest : ℤ → Fin 4) (p q : ℤ) (groups : List (List (Fin 4)))
    (valid padding : List Bool) (i : ℕ) : Tapes 5 0 :=
  RowPaddingBlock.bank (filled (putWord source p groups.flatten) p (consumed groups i).length blank)
    (putWord dest q (consumed (padded groups (Counter.value padding)) i))
    (p+(consumed groups i).length)
    (q+(consumed (padded groups (Counter.value padding)) i).length) valid padding

/-- Both binary countdowns are real tapes. Each consumed's valid cells are moved
and every added zero bit is physically written, with exact resulting banks. -/
theorem pad_loop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length) :
    HoareTime program
      (fun v => v = bank (putWord source p groups.flatten) dest p q valid padding count)
      (fun v => v = bank (filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (padded groups (Counter.value padding)).flatten)
        (p+groups.flatten.length) (q+(padded groups (Counter.value padding)).flatten.length)
        valid padding count)
      (groups.length*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +7*count.length+16) := by
  let cost := 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33
  have hb : ∀ i < groups.length,
      HoareTime RowPaddingBlock.program
        (fun v => v = state source dest p q groups valid padding i)
        (fun v => v = state source dest p q groups valid padding (i+1)) cost := by
    intro i hi
    let f := filled (putWord source p groups.flatten) p (consumed groups i).length blank
    let g := putWord dest q (consumed (padded groups (Counter.value padding)) i)
    have h := RowPaddingBlock.pad_hoare f g (p+(consumed groups i).length)
      (q+(consumed (padded groups (Counter.value padding)) i).length) groups[i] valid padding
      (hv _ (List.getElem_mem hi))
    have hp := consumed_step groups i hi
    have hpp := consumed_step (padded groups (Counter.value padding)) i (by simpa [padded] using hi)
    simp only [padded,List.getElem_map] at hpp
    change consumed (padded groups (Counter.value padding)) (i+1) =
      consumed (padded groups (Counter.value padding)) i ++
        (groups[i]++List.replicate (Counter.value padding) (bitSymbol false)) at hpp
    have hview := current_view source p groups i hi
    change putWord f (p+(consumed groups i).length) groups[i] = f at hview
    rw [hview] at h
    simp only [f,CountedRawFill.filled_adjacent] at h
    have hg : putWord g (q+(consumed (padded groups (Counter.value padding)) i).length)
        (groups[i]++List.replicate (Counter.value padding) (bitSymbol false)) =
        putWord dest q (consumed (padded groups (Counter.value padding)) (i+1)) := by
      rw [hpp]
      exact putWord_append_forward dest q _ _
    rw [hg] at h
    have hcost : 7*groups[i].length+7*valid.length+16+1+7*Counter.value padding+7*padding.length+16 = cost := by
      dsimp [cost]; rw [hv _ (List.getElem_mem hi)]; omega
    rw [hcost] at h
    simpa only [state,hp,hpp,List.length_append,List.length_replicate,Nat.cast_add,
      add_assoc] using h
  have h := CountedLoopReuse.loop_hoare RowPaddingBlock.program count groups.length
    (state source dest p q groups valid padding) (fun _ => cost) hc hb
  have hp : consumed groups groups.length = groups.flatten := by simp [consumed]
  have hpp : consumed (padded groups (Counter.value padding)) groups.length =
      (padded groups (Counter.value padding)).flatten := by
    have hl : (padded groups (Counter.value padding)).length = groups.length := by simp [padded]
    rw [← hl]; simp [consumed]
  apply h.consequence ?_ ?_ ?_
  · intro v hvv
    simpa [state,bank,consumed,putWord] using hvv
  · intro v hvv
    simpa only [state,hp,hpp,bank] using hvv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    dsimp [cost]
    ring_nf
    exact le_rfl

def cropProgram : Program 7 (7+(36+5)+4) 0 := CountedLoopReuse.program RowPaddingBlock.cropProgram

def cropState (source dest : ℤ → Fin 4) (p q : ℤ) (groups : List (List (Fin 4)))
    (valid padding : List Bool) (i : ℕ) : Tapes 5 0 :=
  RowPaddingBlock.bank
    (filled (putWord source p (padded groups (Counter.value padding)).flatten)
      p (consumed (padded groups (Counter.value padding)) i).length blank)
    (putWord dest q (consumed groups i))
    (p+(consumed (padded groups (Counter.value padding)) i).length)
    (q+(consumed groups i).length) valid padding

/-- Both binary countdowns are real tapes. Each consumed's valid cells are moved
and every added zero bit is physically written, with exact resulting banks. -/
theorem crop_loop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length) :
    HoareTime cropProgram
      (fun v => v = bank (putWord source p (padded groups (Counter.value padding)).flatten) dest p q valid padding count)
      (fun v => v = bank (filled (putWord source p (padded groups (Counter.value padding)).flatten)
        p (padded groups (Counter.value padding)).flatten.length blank)
        (putWord dest q groups.flatten)
        (p+(padded groups (Counter.value padding)).flatten.length) (q+groups.flatten.length)
        valid padding count)
      (groups.length*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +7*count.length+16) := by
  let cost := 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33
  have hb : ∀ i < groups.length,
      HoareTime RowPaddingBlock.cropProgram
        (fun v => v = cropState source dest p q groups valid padding i)
        (fun v => v = cropState source dest p q groups valid padding (i+1)) cost := by
    intro i hi
    let f := filled (putWord source p (padded groups (Counter.value padding)).flatten)
      p (consumed (padded groups (Counter.value padding)) i).length blank
    let g := putWord dest q (consumed groups i)
    have h := RowPaddingBlock.crop_hoare f g (p+(consumed (padded groups (Counter.value padding)) i).length)
      (q+(consumed groups i).length) groups[i] valid padding
      (hv _ (List.getElem_mem hi))
    have hp := consumed_step groups i hi
    have hpp := consumed_step (padded groups (Counter.value padding)) i (by simpa [padded] using hi)
    simp only [padded,List.getElem_map] at hpp
    change consumed (padded groups (Counter.value padding)) (i+1) =
      consumed (padded groups (Counter.value padding)) i ++
        (groups[i]++List.replicate (Counter.value padding) (bitSymbol false)) at hpp
    have hwhole := current_view source p (padded groups (Counter.value padding)) i
      (by simpa [padded] using hi)
    simp only [padded,List.getElem_map] at hwhole
    change putWord f (p+(consumed (padded groups (Counter.value padding)) i).length)
      (groups[i]++List.replicate (Counter.value padding) (bitSymbol false)) = f at hwhole
    have hview := WordSegments.middle f
      (p+(consumed (padded groups (Counter.value padding)) i).length) [] groups[i]
      (List.replicate (Counter.value padding) (bitSymbol false))
    simp only [List.nil_append,List.length_nil,Nat.cast_zero,add_zero,hwhole] at hview
    rw [hview] at h
    simp only [f,CountedRawFill.filled_adjacent] at h
    have hg : putWord g (q+(consumed groups i).length) groups[i] =
        putWord dest q (consumed groups (i+1)) := by
      rw [hp]
      exact putWord_append_forward dest q _ _
    rw [hg] at h
    have hcost : 7*groups[i].length+7*valid.length+16+1+7*Counter.value padding+7*padding.length+16 = cost := by
      dsimp [cost]; rw [hv _ (List.getElem_mem hi)]; omega
    rw [hcost] at h
    simpa only [cropState,hp,hpp,List.length_append,List.length_replicate,Nat.cast_add,
      add_assoc] using h
  have h := CountedLoopReuse.loop_hoare RowPaddingBlock.cropProgram count groups.length
    (cropState source dest p q groups valid padding) (fun _ => cost) hc hb
  have hp : consumed groups groups.length = groups.flatten := by simp [consumed]
  have hpp : consumed (padded groups (Counter.value padding)) groups.length =
      (padded groups (Counter.value padding)).flatten := by
    have hl : (padded groups (Counter.value padding)).length = groups.length := by simp [padded]
    rw [← hl]; simp [consumed]
  apply h.consequence ?_ ?_ ?_
  · intro v hvv
    simpa [cropState,bank,consumed,putWord] using hvv
  · intro v hvv
    simpa only [cropState,hp,hpp,bank] using hvv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    dsimp [cost]
    ring_nf
    exact le_rfl

end IntegerMultBounds.Machine.RowPaddingStream

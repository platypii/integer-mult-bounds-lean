import IntegerMultBounds.Machine.RowPaddingStream
import IntegerMultBounds.Machine.RowPaddingReset

/-! Complete physical row-padding wrapper, including both clock markers,
immutable countdown use, full head restoration and clock cleanup. -/
namespace IntegerMultBounds.Machine.RowPaddingExecution

def clockBank (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool)
    (clock : ℤ → Fin 4) (r : ℤ) : Tapes 7 0 :=
  ⟨![p,q,r,1,1,r,1],![source,dest,clock,CountedCopyReuse.binary valid,
    CountedCopyReuse.binary padding,clock,CountedCopyReuse.binary count]⟩

theorem marked_bank (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) :
    clockBank source dest p q valid padding count CountedCopyReuse.empty 1 =
      RowPaddingStream.bank source dest p q valid padding count := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def clockCell (symbol : Fin 4) (m : Move) : Program 7 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then
    some (1,fun i => if i = 2 ∨ i = 5 then (symbol,m) else (sy i,Move.stay)) else none

theorem clock_cell_hoare (symbol : Fin 4) (m : Move) (source dest : ℤ → Fin 4)
    (p q : ℤ) (valid padding count : List Bool) (clock : ℤ → Fin 4) (r : ℤ) :
    HoareTime (clockCell symbol m)
      (fun v => v = clockBank source dest p q valid padding count clock r)
      (fun v => v = clockBank source dest p q valid padding count
        (Function.update clock r symbol) (r+m.offset)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(clockBank source dest p q valid padding count
    (Function.update clock r symbol) (r+m.offset)).head,
    (clockBank source dest p q valid padding count
    (Function.update clock r symbol) (r+m.offset)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,clockCell,Tapes.start,clockBank,↓reduceIte]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [Move.offset]
    · funext i z; fin_cases i <;> simp [Function.update_apply] <;> simp_all
  · simp [step,clockCell]

def markProgram : Program 7 2 0 := clockCell separator Move.right
def clearProgram : Program 7 4 0 := seq (clockCell blank Move.left) (clockCell blank Move.stay)

theorem mark_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) :
    HoareTime markProgram
      (fun v => v = clockBank source dest p q valid padding count (fun _ => blank) 0)
      (fun v => v = RowPaddingStream.bank source dest p q valid padding count) 1 := by
  have he : Function.update (fun _ : ℤ => blank) 0 separator = CountedCopyReuse.empty := by
    funext z; simp [Function.update_apply,CountedCopyReuse.empty]
  simpa only [markProgram,Move.offset,zero_add,he,marked_bank] using
    clock_cell_hoare separator Move.right source dest p q valid padding count (fun _ => blank) 0

theorem clear_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) :
    HoareTime clearProgram
      (fun v => v = RowPaddingStream.bank source dest p q valid padding count)
      (fun v => v = clockBank source dest p q valid padding count (fun _ => blank) 0) 3 := by
  have he : Function.update CountedCopyReuse.empty 1 blank = CountedCopyReuse.empty := by
    apply Function.update_eq_self_iff.mpr
    simp [CountedCopyReuse.empty]
  have hz : Function.update CountedCopyReuse.empty 0 blank = (fun _ : ℤ => blank) := by
    funext z; by_cases h : z = 0 <;> simp [CountedCopyReuse.empty,h]
  have h := clock_cell_hoare blank Move.left source dest p q valid padding count CountedCopyReuse.empty 1
  simp only [Move.offset,show (1:ℤ)+(-1)=0 by rfl,he,marked_bank] at h
  have hh := clock_cell_hoare blank Move.stay source dest p q valid padding count CountedCopyReuse.empty 0
  simp only [Move.offset,add_zero,hz] at hh
  exact h.seq hh

def resetProgram : Program 7 (7+(36+5)+4) 0 := CountedLoopReuse.program RowPaddingReset.padProgram

theorem reset_loop_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) :
    HoareTime resetProgram (fun v => v = RowPaddingStream.bank source dest
        (p+Counter.value count*Counter.value valid)
        (q+Counter.value count*(Counter.value valid+Counter.value padding)) valid padding count)
      (fun v => v = RowPaddingStream.bank source dest p q valid padding count)
      (Counter.value count*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +7*count.length+16) := by
  let v := fun i : ℕ => RowPaddingBlock.bank source dest
    (p+Counter.value count*Counter.value valid-i*Counter.value valid)
    (q+Counter.value count*(Counter.value valid+Counter.value padding)-
      i*(Counter.value valid+Counter.value padding)) valid padding
  let cost := 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33
  have hb : ∀ i < Counter.value count, HoareTime RowPaddingReset.padProgram
      (fun w => w = v i) (fun w => w = v (i+1)) cost := by
    intro i _
    have h := RowPaddingReset.pad_hoare source dest
      (p+Counter.value count*Counter.value valid-i*Counter.value valid)
      (q+Counter.value count*(Counter.value valid+Counter.value padding)-
        i*(Counter.value valid+Counter.value padding)) valid padding
    have he : ∀ a b : ℤ, a-i*b-b = a-((i+1 : ℕ) : ℤ)*b := by intro a b; push_cast; ring
    have he' : ∀ a b c : ℤ, a-i*(b+c)-b-c = a-((i+1 : ℕ) : ℤ)*(b+c) := by
      intro a b c; push_cast; ring
    simpa only [v,cost,he,he'] using h
  have h := CountedLoopReuse.loop_hoare RowPaddingReset.padProgram count (Counter.value count)
    v (fun _ => cost) rfl hb
  apply h.consequence ?_ ?_ ?_
  · intro w hw; simpa only [v,Nat.cast_zero,zero_mul,sub_zero,RowPaddingStream.bank] using hw
  · intro w hw
    simpa only [v,add_sub_cancel_right,RowPaddingStream.bank] using hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    dsimp [cost]
    ring_nf
    exact le_rfl

def cropResetProgram : Program 7 (7+(36+5)+4) 0 := CountedLoopReuse.program RowPaddingReset.cropProgram

theorem crop_reset_loop_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding count : List Bool) :
    HoareTime cropResetProgram (fun v => v = RowPaddingStream.bank source dest
        (p+Counter.value count*(Counter.value valid+Counter.value padding))
        (q+Counter.value count*Counter.value valid) valid padding count)
      (fun v => v = RowPaddingStream.bank source dest p q valid padding count)
      (Counter.value count*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +7*count.length+16) := by
  let v := fun i : ℕ => RowPaddingBlock.bank source dest
    (p+Counter.value count*(Counter.value valid+Counter.value padding)-
      i*(Counter.value valid+Counter.value padding))
    (q+Counter.value count*Counter.value valid-i*Counter.value valid) valid padding
  let cost := 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+33
  have hb : ∀ i < Counter.value count, HoareTime RowPaddingReset.cropProgram
      (fun w => w = v i) (fun w => w = v (i+1)) cost := by
    intro i _
    have h := RowPaddingReset.crop_hoare source dest
      (p+Counter.value count*(Counter.value valid+Counter.value padding)-
        i*(Counter.value valid+Counter.value padding))
      (q+Counter.value count*Counter.value valid-i*Counter.value valid) valid padding
    have he : ∀ a b : ℤ, a-i*b-b = a-((i+1 : ℕ) : ℤ)*b := by intro a b; push_cast; ring
    have he' : ∀ a b c : ℤ, a-i*(b+c)-b-c = a-((i+1 : ℕ) : ℤ)*(b+c) := by
      intro a b c; push_cast; ring
    simpa only [v,cost,he,he'] using h
  have h := CountedLoopReuse.loop_hoare RowPaddingReset.cropProgram count (Counter.value count)
    v (fun _ => cost) rfl hb
  apply h.consequence ?_ ?_ ?_
  · intro w hw; simpa only [v,Nat.cast_zero,zero_mul,sub_zero,RowPaddingStream.bank] using hw
  · intro w hw
    simpa only [v,add_sub_cancel_right,RowPaddingStream.bank] using hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    dsimp [cost]
    ring_nf
    exact le_rfl

theorem flattened_length (groups : List (List (Fin 4))) (n : ℕ)
    (hn : ∀ xs ∈ groups, xs.length = n) : groups.flatten.length = groups.length*n := by
  induction groups with
  | nil => simp
  | cons xs groups ih =>
    have hx := hn xs (by simp)
    have ht := ih (by intro ys hy; exact hn ys (by simp [hy]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hx,ht]
    ring

def program : Program 7 (2+(52+(52+4))) 0 :=
  seq markProgram (seq RowPaddingStream.program (seq resetProgram clearProgram))

/-- Complete padding with clean work clocks at both boundaries and payload
heads restored to their original origins. Count descriptors are preserved. -/
theorem pad_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length) :
    HoareTime program
      (fun v => v = clockBank (putWord source p groups.flatten) dest p q valid padding count (fun _ => blank) 0)
      (fun v => v = clockBank
        (CountedRawFill.filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (RowPaddingStream.padded groups (Counter.value padding)).flatten)
        p q valid padding count (fun _ => blank) 0)
      (2*groups.length*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +14*count.length+39) := by
  have hl := flattened_length groups (Counter.value valid) (by intro xs hx; exact (hv xs hx).symm)
  have hp := flattened_length (RowPaddingStream.padded groups (Counter.value padding))
    (Counter.value valid+Counter.value padding) (by
      intro xs hx
      obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
      simp only [List.length_append,List.length_replicate]
      rw [← hv ys hy])
  have hplen : (RowPaddingStream.padded groups (Counter.value padding)).length = groups.length := by
    simp [RowPaddingStream.padded]
  rw [hplen] at hp
  let erased := CountedRawFill.filled (putWord source p groups.flatten) p groups.flatten.length blank
  let output := putWord dest q (RowPaddingStream.padded groups (Counter.value padding)).flatten
  have hm := mark_hoare (putWord source p groups.flatten) dest p q valid padding count
  have hs := RowPaddingStream.pad_loop_hoare source dest p q groups valid padding count hv hc
  have hr := reset_loop_hoare erased output p q valid padding count
  rw [hc] at hr
  have hheads : (groups.flatten.length : ℤ) = (groups.length : ℤ)*Counter.value valid := by
    exact_mod_cast hl
  have hpheads : ((RowPaddingStream.padded groups (Counter.value padding)).flatten.length : ℤ) =
      (groups.length : ℤ)*(Counter.value valid+Counter.value padding) := by exact_mod_cast hp
  rw [hheads,hpheads] at hs
  have h := hm.seq (hs.seq (hr.seq (clear_hoare erased output p q valid padding count)))
  simpa only [program,erased,output,Nat.add_assoc] using h.consequence (fun _ hh => hh)
    (fun _ hh => hh) (by ring_nf; exact le_rfl)
def cropProgram : Program 7 (2+(52+(52+4))) 0 :=
  seq markProgram (seq RowPaddingStream.cropProgram (seq cropResetProgram clearProgram))

/-- Complete padding with clean work clocks at both boundaries and payload
heads restored to their original origins. Count descriptors are preserved. -/
theorem crop_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length) :
    HoareTime cropProgram
      (fun v => v = clockBank (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten) dest p q valid padding count (fun _ => blank) 0)
      (fun v => v = clockBank
        (CountedRawFill.filled (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten)
          p (RowPaddingStream.padded groups (Counter.value padding)).flatten.length blank)
        (putWord dest q groups.flatten)
        p q valid padding count (fun _ => blank) 0)
      (2*groups.length*(7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39)
        +14*count.length+39) := by
  have hl := flattened_length groups (Counter.value valid) (by intro xs hx; exact (hv xs hx).symm)
  have hp := flattened_length (RowPaddingStream.padded groups (Counter.value padding))
    (Counter.value valid+Counter.value padding) (by
      intro xs hx
      obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
      simp only [List.length_append,List.length_replicate]
      rw [← hv ys hy])
  have hplen : (RowPaddingStream.padded groups (Counter.value padding)).length = groups.length := by
    simp [RowPaddingStream.padded]
  rw [hplen] at hp
  let erased := CountedRawFill.filled (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten)
    p (RowPaddingStream.padded groups (Counter.value padding)).flatten.length blank
  let output := putWord dest q groups.flatten
  have hm := mark_hoare (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten) dest p q valid padding count
  have hs := RowPaddingStream.crop_loop_hoare source dest p q groups valid padding count hv hc
  have hr := crop_reset_loop_hoare erased output p q valid padding count
  rw [hc] at hr
  have hheads : (groups.flatten.length : ℤ) = (groups.length : ℤ)*Counter.value valid := by
    exact_mod_cast hl
  have hpheads : ((RowPaddingStream.padded groups (Counter.value padding)).flatten.length : ℤ) =
      (groups.length : ℤ)*(Counter.value valid+Counter.value padding) := by exact_mod_cast hp
  rw [hheads,hpheads] at hs
  have h := hm.seq (hs.seq (hr.seq (clear_hoare erased output p q valid padding count)))
  simpa only [cropProgram,erased,output,Nat.add_assoc] using h.consequence (fun _ hh => hh)
    (fun _ hh => hh) (by ring_nf; exact le_rfl)

theorem canonical_cost (valid padding count : List Bool)
    (hv : GrowingCounterData.Canonical valid) (hm : GrowingCounterData.Canonical padding)
    (hc : GrowingCounterData.Canonical count)
    (hspan : 0 < Counter.value valid+Counter.value padding) :
    2*Counter.value count*(7*Counter.value valid+7*valid.length+
      7*Counter.value padding+7*padding.length+39)+14*count.length+39 ≤
      148*Counter.value count*(Counter.value valid+Counter.value padding)+53 := by
  have hwv := GrowingCounterData.canonical_width valid hv
  have hwm := GrowingCounterData.canonical_width padding hm
  have hwc := GrowingCounterData.canonical_width count hc
  have hnv := Nat.log2_le_self (Counter.value valid)
  have hnm := Nat.log2_le_self (Counter.value padding)
  have hnc := Nat.log2_le_self (Counter.value count)
  have ha : 7*Counter.value valid+7*valid.length+7*Counter.value padding+7*padding.length+39 ≤
      14*(Counter.value valid+Counter.value padding)+53 := by omega
  have hb := Nat.mul_le_mul_left (2*Counter.value count) ha
  have hd := Nat.mul_le_mul_left (Counter.value count) (by omega : 1 ≤ Counter.value valid+Counter.value padding)
  nlinarith

/-- Canonical descriptors make the complete padding wrapper linear in the
padded volume, including countdown setup, scans, rewinds and work cleanup. -/
theorem pad_linear (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length)
    (cv : GrowingCounterData.Canonical valid) (cm : GrowingCounterData.Canonical padding)
    (cc : GrowingCounterData.Canonical count)
    (hspan : 0 < Counter.value valid+Counter.value padding) :
    HoareTime program
      (fun v => v = clockBank (putWord source p groups.flatten) dest p q valid padding count (fun _ => blank) 0)
      (fun v => v = clockBank
        (CountedRawFill.filled (putWord source p groups.flatten) p groups.flatten.length blank)
        (putWord dest q (RowPaddingStream.padded groups (Counter.value padding)).flatten)
        p q valid padding count (fun _ => blank) 0)
      (148*groups.length*(Counter.value valid+Counter.value padding)+53) := by
  have h := canonical_cost valid padding count cv cm cc hspan
  rw [hc] at h
  exact (pad_hoare source dest p q groups valid padding count hv hc).consequence
    (fun _ hh => hh) (fun _ hh => hh) h

/-- Cropping pays for every padding cell and restores both payload origins. -/
theorem crop_linear (source dest : ℤ → Fin 4) (p q : ℤ)
    (groups : List (List (Fin 4))) (valid padding count : List Bool)
    (hv : ∀ xs ∈ groups, Counter.value valid = xs.length)
    (hc : Counter.value count = groups.length)
    (cv : GrowingCounterData.Canonical valid) (cm : GrowingCounterData.Canonical padding)
    (cc : GrowingCounterData.Canonical count)
    (hspan : 0 < Counter.value valid+Counter.value padding) :
    HoareTime cropProgram
      (fun v => v = clockBank (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten)
        dest p q valid padding count (fun _ => blank) 0)
      (fun v => v = clockBank
        (CountedRawFill.filled (putWord source p (RowPaddingStream.padded groups (Counter.value padding)).flatten)
          p (RowPaddingStream.padded groups (Counter.value padding)).flatten.length blank)
        (putWord dest q groups.flatten) p q valid padding count (fun _ => blank) 0)
      (148*groups.length*(Counter.value valid+Counter.value padding)+53) := by
  have h := canonical_cost valid padding count cv cm cc hspan
  rw [hc] at h
  exact (crop_hoare source dest p q groups valid padding count hv hc).consequence
    (fun _ hh => hh) (fun _ hh => hh) h

end IntegerMultBounds.Machine.RowPaddingExecution

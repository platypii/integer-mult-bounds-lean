import IntegerMultBounds.Machine.ScalingSplitRewind
import IntegerMultBounds.Machine.ScalingScatter

/-! Literal concatenation of fixed many end-positioned buffer streams. Each
stage physically rewinds its source and then copies it to the advancing output.
All buffer cells and endpoint heads survive, as do all immutable descriptors
and the reusable clock. -/

namespace IntegerMultBounds.Machine.ScalingConcatenate

open ScalingSplit (TapeCount bank slots widthSum)

/-- Reverse the local copy's source/destination roles. -/
def reverseSlots : Fin (4+0) ≃ Fin 4 := Equiv.swap 0 1

def copyProgram : Program 4 16 0 := Placement.placed CountedCopyReuse.program reverseSlots

private theorem active_copy (dest source : ℤ → Fin 4) (q p : ℤ) (bs : List Bool) :
    Placement.active reverseSlots
      (CountedCopyReuse.bank dest source CountedCopyReuse.empty (CountedCopyReuse.binary bs) q p 1 1) =
      CountedCopyReuse.bank source dest CountedCopyReuse.empty (CountedCopyReuse.binary bs) p q 1 1 := by
  unfold Placement.active reverseSlots CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_copy (dest source dest' : ℤ → Fin 4) (q p q' p' : ℤ) (bs : List Bool) :
    Placement.replace reverseSlots
      (CountedCopyReuse.bank dest source CountedCopyReuse.empty (CountedCopyReuse.binary bs) q p 1 1)
      (CountedCopyReuse.bank source dest' CountedCopyReuse.empty (CountedCopyReuse.binary bs) p' q' 1 1) =
      CountedCopyReuse.bank dest' source CountedCopyReuse.empty (CountedCopyReuse.binary bs) q' p' 1 1 := by
  unfold Placement.replace Placement.combine Placement.extra reverseSlots Tapes.reindex Tapes.append
    CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem copy_hoare (dest source : ℤ → Fin 4) (q p : ℤ) (bs : List Bool)
    (xs : List (Fin 4)) (hb : Counter.value bs = xs.length) :
    HoareTime copyProgram
      (fun v => v = CountedCopyReuse.bank dest (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) q p 1 1)
      (fun v => v = CountedCopyReuse.bank (putWord dest q xs) (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) (q+xs.length) (p+xs.length) 1 1)
      (5*xs.length+7*bs.length+16) := by
  have h := Placement.hoare_at (CountedCopyReuse.copy_hoare source dest p q xs bs hb) reverseSlots
    (CountedCopyReuse.bank dest (putWord source p xs) CountedCopyReuse.empty (CountedCopyReuse.binary bs) q p 1 1)
    (active_copy _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_copy _ _ _ _ _ _ _ _

/-- A real rewind followed by the reversed-role copy, including the join. -/
def localProgram : Program 4 32 0 := seq ScalingSplitRewind.localProgram copyProgram

private theorem local_hoare (dest source : ℤ → Fin 4) (q p : ℤ) (bs : List Bool)
    (xs : List (Fin 4)) (hb : Counter.value bs = xs.length) :
    HoareTime localProgram
      (fun v => v = CountedCopyReuse.bank dest (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) q (p+xs.length) 1 1)
      (fun v => v = CountedCopyReuse.bank (putWord dest q xs) (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) (q+xs.length) (p+xs.length) 1 1)
      (10*xs.length+14*bs.length+33) := by
  have ha : Placement.active ScalingSplitRewind.localSlots
      (CountedCopyReuse.bank dest (putWord source p xs) CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) q (p+xs.length) 1 1) =
      CountedSeek.bank (putWord source p xs) (p+xs.length) bs := by
    unfold Placement.active ScalingSplitRewind.localSlots CountedCopyReuse.bank CountedSeek.bank
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at
    (CountedSeek.seek_backward_hoare (putWord source p xs) (p+xs.length) bs)
    ScalingSplitRewind.localSlots _ ha
  have hr : HoareTime ScalingSplitRewind.localProgram
      (fun v => v = CountedCopyReuse.bank dest (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) q (p+xs.length) 1 1)
      (fun v => v = CountedCopyReuse.bank dest (putWord source p xs)
        CountedCopyReuse.empty (CountedCopyReuse.binary bs) q p 1 1)
      (5*xs.length+7*bs.length+16) := by
    apply h.consequence (fun _ hv => hv) _ (by rw [hb])
    rintro v ⟨w,rfl,rfl⟩
    rw [hb]
    simp only [add_sub_cancel_right]
    unfold Placement.replace Placement.combine Placement.extra ScalingSplitRewind.localSlots
      Tapes.reindex Tapes.append CountedCopyReuse.bank CountedSeek.bank
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  exact (hr.seq (copy_hoare dest source q p bs xs hb)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

def stage {c : ℕ} (j : Fin c) : Program (TapeCount c) 32 0 :=
  Placement.placed (u := c+c) localProgram (slots j)

/-- A selected end-positioned stream is appended; all buffer heads end exactly
where they started and all source tape cells survive. -/
theorem stage_hoare {c : ℕ} (j : Fin c) (dest : ℤ → Fin 4)
    (sources : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (q : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin 4))
    (hb : Counter.value (descriptors j) = (words j).length) :
    HoareTime (stage j)
      (fun v => v = bank dest (fun k => putWord (sources k) (origins k) (words k)) descriptors q
        (fun k => origins k+(words k).length))
      (fun v => v = bank (putWord dest q (words j))
        (fun k => putWord (sources k) (origins k) (words k)) descriptors (q+(words j).length)
        (fun k => origins k+(words k).length))
      (10*(words j).length+14*(descriptors j).length+33) := by
  have h := Placement.hoare_at (local_hoare dest (sources j) q (origins j) (descriptors j) (words j) hb)
    (slots j) (bank dest (fun k => putWord (sources k) (origins k) (words k)) descriptors q
      (fun k => origins k+(words k).length)) (ScalingSplit.active_bank j _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [ScalingSplit.replace_bank,Function.update_eq_self,Function.update_eq_self]

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => states n+32

private def haltProgram (c : ℕ) : Program (TapeCount c) 1 0 :=
  ⟨by dsimp [TapeCount]; omega,0,fun _ _ => none⟩

def initialStages (c : ℕ) : (n : ℕ) → n ≤ c → Program (TapeCount c) (states n) 0
  | 0,_ => haltProgram c
  | n+1,hn => seq (initialStages c n (by omega)) (stage ⟨n,by omega⟩)

def program (c : ℕ) : Program (TapeCount c) (states c) 0 := initialStages c c le_rfl

def outputPrefix {c : ℕ} (words : Fin c → List (Fin 4)) (n : ℕ) : List (Fin 4) :=
  ((List.ofFn words).take n).flatten

private theorem prefix_succ {c : ℕ} (words : Fin c → List (Fin 4)) (j : Fin c) :
    outputPrefix words (j.val+1) = outputPrefix words j.val ++ words j := by
  unfold outputPrefix
  rw [List.take_succ_eq_append_getElem (by simp),List.flatten_append]
  simp

theorem initialStages_hoare {c : ℕ} (dest : ℤ → Fin 4)
    (sources : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (q : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin 4))
    (hb : ∀ j, Counter.value (descriptors j) = (words j).length) (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c n hn)
      (fun v => v = bank dest (fun k => putWord (sources k) (origins k) (words k)) descriptors q
        (fun k => origins k+(words k).length))
      (fun v => v = bank (putWord dest q (outputPrefix words n))
        (fun k => putWord (sources k) (origins k) (words k)) descriptors
        (q+(outputPrefix words n).length) (fun k => origins k+(words k).length))
      (10*(outputPrefix words n).length+14*widthSum descriptors n+34*n) := by
  induction n with
  | zero =>
    rintro v rfl
    refine ⟨0,_,by simp [outputPrefix],rfl,rfl,?_⟩
    simp only [outputPrefix,List.take_zero,List.flatten_nil,putWord,List.length_nil,Nat.cast_zero,add_zero]
    rfl
  | succ n ih =>
    have hnc : n < c := by omega
    have h := (ih (by omega)).seq (stage_hoare ⟨n,hnc⟩ (putWord dest q (outputPrefix words n))
      sources descriptors (q+(outputPrefix words n).length) origins words (hb ⟨n,hnc⟩))
    have hp := prefix_succ words ⟨n,hnc⟩
    rw [putWord_append_forward,← hp] at h
    apply h.consequence (fun _ hv => hv) _ _
    · intro v hv
      simpa only [hp,List.length_append,Nat.cast_add,add_assoc] using hv
    · simp only [hp,List.length_append,widthSum,Finset.sum_range_succ,hnc,dite_true]
      omega

/-- Complete fixed-family concatenation from end-positioned buffers. No source
movement is free: every rewind, copy, clock reset and sequence join is charged. -/
theorem concatenate_hoare {c : ℕ} (dest : ℤ → Fin 4)
    (sources : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (q : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin 4))
    (hb : ∀ j, Counter.value (descriptors j) = (words j).length) :
    HoareTime (program c)
      (fun v => v = bank dest (fun k => putWord (sources k) (origins k) (words k)) descriptors q
        (fun k => origins k+(words k).length))
      (fun v => v = bank (putWord dest q (List.ofFn words).flatten)
        (fun k => putWord (sources k) (origins k) (words k)) descriptors
        (q+(List.ofFn words).flatten.length) (fun k => origins k+(words k).length))
      (10*(List.ofFn words).flatten.length+14*widthSum descriptors c+34*c) := by
  have hh := initialStages_hoare dest sources descriptors q origins words hb c le_rfl
  have he : outputPrefix words c = (List.ofFn words).flatten := by
    unfold outputPrefix
    congr 1
    exact List.take_of_length_le (by simp)
  simpa only [program,he] using hh


/-- Canonical descriptor widths sum to at most total payload plus the number
of fixed buffers; empty buffers are allowed. -/
theorem widthSum_le {c : ℕ} (words : Fin c → List (Fin 4))
    (descriptors : Fin c → List Bool)
    (hb : ∀ j, Counter.value (descriptors j) = (words j).length)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (n : ℕ) (hn : n ≤ c) :
    widthSum descriptors n ≤ (outputPrefix words n).length+n := by
  induction n with
  | zero => simp [widthSum,outputPrefix]
  | succ n ih =>
    have hnc : n < c := by omega
    have hi := ih (by omega)
    have hw := GrowingCounterData.canonical_width (descriptors ⟨n,hnc⟩) (hcanonical ⟨n,hnc⟩)
    have hl := Nat.log2_le_self (Counter.value (descriptors ⟨n,hnc⟩))
    rw [hb] at hw hl
    rw [prefix_succ words ⟨n,hnc⟩,List.length_append]
    simp only [widthSum,Finset.sum_range_succ,hnc,dite_true] at hi ⊢
    omega

/-- Full concatenation is linear in payload volume, with only a fixed-coefficient
additive term, including all source rewinds and the restored control state. -/
theorem concatenate_hoare_linear {c : ℕ} (dest : ℤ → Fin 4)
    (sources : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (q : ℤ) (origins : Fin c → ℤ) (words : Fin c → List (Fin 4))
    (hb : ∀ j, Counter.value (descriptors j) = (words j).length)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j)) :
    HoareTime (program c)
      (fun v => v = bank dest (fun k => putWord (sources k) (origins k) (words k)) descriptors q
        (fun k => origins k+(words k).length))
      (fun v => v = bank (putWord dest q (List.ofFn words).flatten)
        (fun k => putWord (sources k) (origins k) (words k)) descriptors
        (q+(List.ofFn words).flatten.length) (fun k => origins k+(words k).length))
      (24*(List.ofFn words).flatten.length+48*c) := by
  have hw := widthSum_le words descriptors hb hcanonical c le_rfl
  have he : outputPrefix words c = (List.ofFn words).flatten := by
    unfold outputPrefix
    congr 1
    exact List.take_of_length_le (by simp)
  rw [he] at hw
  exact (concatenate_hoare dest sources descriptors q origins words hb).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.ScalingConcatenate

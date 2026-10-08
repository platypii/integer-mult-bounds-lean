import IntegerMultBounds.Machine.BlockReverseStreamReuse
import IntegerMultBounds.Machine.ScratchReset
import IntegerMultBounds.Machine.BlockNegationData

/-! Reusable single-fiber coordinate negation. Copy the first block, reverse
its raw tail into scratch, restore the scratch head, and reverse each payload
block into output. The final literal scratch reset restores the entire scratch
background and its original head. All controls are retained and all work clocks
are cleaned, with preparation and every sequential join charged. -/

namespace IntegerMultBounds.Machine.BlockNegationReuse

/-- Source, destination, scratch, reusable inner clock, immutable B descriptor,
immutable tail-length descriptor, mutable outer clock, immutable block count. -/
def bank (source dest scratch : ℤ → Fin 4) (bs tailBits countBits : List Bool)
    (p q r : ℤ) : Tapes 8 0 where
  head := fun i => if i = 0 then p else if i = 1 then q else if i = 2 then r else 1
  tape := fun i => if i = 0 then source else if i = 1 then dest else if i = 2 then scratch
    else if i = 3 ∨ i = 6 then CountedCopyReuse.empty else if i = 4 then CountedCopyReuse.binary bs
    else if i = 5 then CountedCopyReuse.binary tailBits else CountedCopyReuse.binary countBits

def copySlots : Fin (4+4) ≃ Fin 8 where
  toFun := ![0,1,3,4,2,5,6,7]
  invFun := ![0,1,4,2,3,5,6,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def reverseSlots : Fin (4+4) ≃ Fin 8 where
  toFun := ![0,2,3,5,1,4,6,7]
  invFun := ![0,4,1,2,5,3,6,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def seekSlots : Fin (3+5) ≃ Fin 8 where
  toFun := ![2,3,5,0,1,4,6,7]
  invFun := ![3,4,0,1,5,2,6,7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def correctSlots : Fin (6+2) ≃ Fin 8 where
  toFun := ![2,1,3,4,6,7,0,5]
  invFun := ![6,1,0,2,3,7,4,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def copyFirst : Program 8 16 0 := Placement.placed (u := 4) CountedCopyReuse.program copySlots

def reverseTail : Program 8 52 0 := Placement.placed (u := 4) BlockReverseAdvance.program reverseSlots

def seekTail : Program 8 16 0 := Placement.placed (u := 5) CountedSeek.backwardProgram seekSlots

def correctTail : Program 8 68 0 := Placement.placed (u := 2) BlockReverseStreamReuse.program correctSlots

private theorem active_copy (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ) :
    Placement.active (s := 4) copySlots (bank f g h b d c p q r) =
      CountedCopyReuse.bank f g CountedCopyReuse.empty (CountedCopyReuse.binary b) p q 1 1 := by
  unfold Placement.active bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_copy (f g h f' g' : ℤ → Fin 4) (b d c : List Bool) (p q r p' q' : ℤ) :
    Placement.replace (s := 4) copySlots (bank f g h b d c p q r)
      (CountedCopyReuse.bank f' g' CountedCopyReuse.empty (CountedCopyReuse.binary b) p' q' 1 1) =
      bank f' g' h b d c p' q' r := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem copy_hoare (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ)
    (xs : List (Fin 4)) (hb : Counter.value b = xs.length) :
    HoareTime copyFirst
      (fun v => v = bank (putWord f p xs) g h b d c p q r)
      (fun v => v = bank (putWord f p xs) (putWord g q xs) h b d c
        (p+xs.length) (q+xs.length) r) (5*xs.length+7*b.length+16) := by
  have hh := Placement.hoare_at (CountedCopyReuse.copy_hoare f g p q xs b hb) copySlots
    (bank (putWord f p xs) g h b d c p q r) (active_copy _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_copy _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem active_reverse (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ) :
    Placement.active (s := 4) reverseSlots (bank f g h b d c p q r) =
      BlockReverseAdvance.bank f h d p r := by
  unfold Placement.active bank BlockReverseAdvance.bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_reverse (f g h f' h' : ℤ → Fin 4) (b d c : List Bool) (p q r p' r' : ℤ) :
    Placement.replace (s := 4) reverseSlots (bank f g h b d c p q r)
      (BlockReverseAdvance.bank f' h' d p' r') = bank f' g h' b d c p' q r' := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank BlockReverseAdvance.bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem reverse_hoare (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ)
    (xs : List (Fin 4)) (hd : Counter.value d = xs.length) :
    HoareTime reverseTail
      (fun v => v = bank (putWord f p xs) g h b d c p q r)
      (fun v => v = bank (putWord f p xs) g (putWord h r xs.reverse) b d c
        (p+xs.length) q (r+xs.length)) (15*xs.length+21*d.length+54) := by
  have hh := Placement.hoare_at (BlockReverseAdvance.reverse_hoare f h p r xs d hd) reverseSlots
    (bank (putWord f p xs) g h b d c p q r) (active_reverse _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_reverse _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem active_seek (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ) :
    Placement.active (s := 3) seekSlots (bank f g h b d c p q r) = CountedSeek.bank h r d := by
  unfold Placement.active bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_seek (f g h h' : ℤ → Fin 4) (b d c : List Bool) (p q r r' : ℤ) :
    Placement.replace (s := 3) seekSlots (bank f g h b d c p q r) (CountedSeek.bank h' r' d) =
      bank f g h' b d c p q r' := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem seek_hoare (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ) :
    HoareTime seekTail (fun v => v = bank f g h b d c p q r)
      (fun v => v = bank f g h b d c p q (r-Counter.value d)) (5*Counter.value d+7*d.length+16) := by
  have hh := Placement.hoare_at (CountedSeek.seek_backward_hoare h r d) seekSlots
    (bank f g h b d c p q r) (active_seek _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_seek _ _ _ _ _ _ _ _ _ _ _

private theorem active_correct (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ) :
    Placement.active (s := 6) correctSlots (bank f g h b d c p q r) =
      CountedLoopReuse.bank (BlockReverseAdvance.bank h g b r q) CountedCopyReuse.empty (CountedCopyReuse.binary c) 1 1 := by
  unfold Placement.active bank CountedLoopReuse.bank CountedLoopReuse.controls BlockReverseAdvance.bank CountedCopyReuse.bank Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_correct (f g h g' h' : ℤ → Fin 4) (b d c : List Bool)
    (p q r q' r' : ℤ) :
    Placement.replace (s := 6) correctSlots (bank f g h b d c p q r)
      (CountedLoopReuse.bank (BlockReverseAdvance.bank h' g' b r' q') CountedCopyReuse.empty (CountedCopyReuse.binary c) 1 1) =
      bank f g' h' b d c p q' r' := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedLoopReuse.bank CountedLoopReuse.controls BlockReverseAdvance.bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem correct_hoare (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ)
    (blocks : List (List (Fin 4))) (B : ℕ) (hu : BlockRotationData.Uniform B blocks)
    (hb : Counter.value b = B) (hc : Counter.value c = blocks.length) :
    HoareTime correctTail
      (fun v => v = bank f g (putWord h r blocks.flatten) b d c p q r)
      (fun v => v = bank f (putWord g q (blocks.map List.reverse).flatten) (putWord h r blocks.flatten)
        b d c p (q+((blocks.length*B : ℕ) : ℤ))
        (r+((blocks.length*B : ℕ) : ℤ)))
      (blocks.length*(BlockReverseStream.bodyBound B b+6)+7*c.length+16) := by
  have hh := Placement.hoare_at (BlockReverseStreamReuse.reverse_hoare h g r q blocks B hu b c hb hc)
    correctSlots (bank f g (putWord h r blocks.flatten) b d c p q r) (active_correct _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_correct _ _ _ _ _ _ _ _ _ _ _ _ _

def cleanTail : Program 8 50 0 := Placement.placed (u := 5) ScratchReset.program seekSlots

private theorem clean_hoare (f g h : ℤ → Fin 4) (b d c : List Bool) (p q r : ℤ)
    (xs : List (Fin 4)) (hd : Counter.value d = xs.length)
    (hblank : ∀ z, r ≤ z → z < r+xs.length → h z = blank) :
    HoareTime cleanTail (fun v => v = bank f g (putWord h r xs) b d c p q (r+xs.length))
      (fun v => v = bank f g h b d c p q r) (17*xs.length+21*d.length+50) := by
  have hh := Placement.hoare_at (ScratchReset.reset_word_hoare h r xs d hd hblank) seekSlots
    (bank f g (putWord h r xs) b d c p q (r+xs.length)) (active_seek _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_seek _ _ _ _ _ _ _ _ _ _ _

/-- Five actual routines and precisely four charged sequential joins. -/
def program : Program 8 202 0 := seq (seq (seq (seq copyFirst reverseTail) seekTail) correctTail) cleanTail

def bound (B n : ℕ) (b d c : List Bool) : ℕ :=
  5*B+37*(n*B)+7*b.length+49*d.length+
    n*(BlockReverseStream.bodyBound B b+6)+7*c.length+156

/-- Coordinate negation fixes the first block and reverses the remaining block
order while preserving every block's internal payload. Scratch is restored to
its original background and head. All descriptors and both work clocks retain
their reusable states, including at zero tail length. -/
theorem negate_hoare (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (first : List (Fin 4)) (tail : List (List (Fin 4))) (B : ℕ)
    (hf : first.length = B) (hu : BlockRotationData.Uniform B tail)
    (b d c : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = tail.length*B) (hc : Counter.value c = tail.length)
    (hblank : ∀ z, r ≤ z → z < r+tail.flatten.length → scratch z = blank) :
    HoareTime program
      (fun v => v = bank (putWord source p (first::tail).flatten) dest scratch b d c p q r)
      (fun v => v = bank (putWord source p (first::tail).flatten)
        (putWord dest q (BlockNegationData.negate (first::tail)).flatten)
        scratch b d c
        (p+(first::tail).flatten.length) (q+(first::tail).flatten.length) r)
      (bound B tail.length b d c) := by
  let input := putWord source p (first++tail.flatten)
  let firstOut := putWord dest q first
  let raw := putWord scratch r tail.flatten.reverse
  have hvolume : tail.flatten.length = tail.length*B := BlockRotationData.uniform_volume B tail hu
  have hfirst : putWord input p first = input := by
    simpa only [List.nil_append,List.length_nil,Nat.cast_zero,add_zero] using
      WordSegments.middle source p [] first tail.flatten
  have htail : putWord input (p+B) tail.flatten = input := by
    simpa only [List.append_nil,hf] using WordSegments.middle source p first tail.flatten []
  have h₀ := copy_hoare input dest scratch b d c p q r first (by simpa only [hf] using hb)
  rw [hfirst,hf] at h₀
  have h₁ := reverse_hoare input firstOut scratch b d c (p+B) (q+B) r tail.flatten
    (by simpa only [hvolume] using hd)
  rw [htail,hvolume] at h₁
  have h₂ := seek_hoare input firstOut raw b d c (p+B+((tail.length*B : ℕ) : ℤ)) (q+B)
    (r+((tail.length*B : ℕ) : ℤ))
  rw [hd,add_sub_cancel_right] at h₂
  have h₃ := correct_hoare input firstOut scratch b d c (p+B+((tail.length*B : ℕ) : ℤ))
    (q+B) r (BlockNegationData.rawBlocks tail) B (BlockNegationData.rawBlocks_uniform B tail hu)
    hb (by simpa only [BlockNegationData.rawBlocks_length] using hc)
  rw [BlockNegationData.rawBlocks_flatten,BlockNegationData.corrected_rawBlocks,
    BlockNegationData.rawBlocks_length] at h₃
  have hout : putWord firstOut (q+B) tail.reverse.flatten =
      putWord dest q (BlockNegationData.negate (first::tail)).flatten := by
    rw [← hf]
    change putWord (putWord dest q first) (q+first.length) tail.reverse.flatten = _
    rw [putWord_append_forward]
    rfl
  rw [hout] at h₃
  have h₄ := clean_hoare input (putWord dest q (BlockNegationData.negate (first::tail)).flatten)
    scratch b d c (p+B+((tail.length*B : ℕ) : ℤ)) (q+B+((tail.length*B : ℕ) : ℤ)) r
    tail.flatten.reverse (by simpa only [List.length_reverse,hvolume] using hd)
    (by simpa only [List.length_reverse] using hblank)
  rw [List.length_reverse,hvolume] at h₄
  have h := (((h₀.seq h₁).seq h₂).seq h₃).seq h₄
  apply h.consequence
  · intro v hv
    simpa only [input,List.flatten_cons] using hv
  · intro v hv
    simpa only [input,raw,List.flatten_cons,List.length_append,hf,hvolume,Nat.cast_add,add_assoc] using hv
  · dsimp only [bound]
    omega

/-- Explicit linear-volume bound for positive block width and canonical-sized
prepared descriptors. The additive constant pays for the fixed joins and scans. -/
theorem linear_bound (B n : ℕ) (b d c : List Bool) (hB : 1 ≤ B)
    (hb : b.length ≤ B+1) (hd : d.length ≤ n*B+1) (hc : c.length ≤ n+1) :
    bound B n b d c ≤ 210*(B+n*B)+219 := by
  have hstream := BlockReverseStreamReuse.linear_bound B n b c hB hb hc
  dsimp only [bound]
  omega

private theorem canonical_width_le (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs+1 := by
  have hw := GrowingCounterData.canonical_width bs h
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

/-- Complete single-fiber negation runs in linear payload volume. This includes
all scratch positioning and cleanup, retaining every immutable descriptor and
restoring both mutable clocks and the complete initially blank scratch interval. -/
theorem negate_hoare_linear (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (first : List (Fin 4)) (tail : List (List (Fin 4))) (B : ℕ)
    (hf : first.length = B) (hu : BlockRotationData.Uniform B tail) (hB : 1 ≤ B)
    (b d c : List Bool) (hb : Counter.value b = B)
    (hd : Counter.value d = tail.length*B) (hc : Counter.value c = tail.length)
    (cb : GrowingCounterData.Canonical b) (cd : GrowingCounterData.Canonical d)
    (cc : GrowingCounterData.Canonical c)
    (hblank : ∀ z, r ≤ z → z < r+tail.flatten.length → scratch z = blank) :
    HoareTime program
      (fun v => v = bank (putWord source p (first::tail).flatten) dest scratch b d c p q r)
      (fun v => v = bank (putWord source p (first::tail).flatten)
        (putWord dest q (BlockNegationData.negate (first::tail)).flatten)
        scratch b d c
        (p+(first::tail).flatten.length) (q+(first::tail).flatten.length) r)
      (210*(first::tail).flatten.length+219) := by
  have wb := canonical_width_le b cb
  have wd := canonical_width_le d cd
  have wc := canonical_width_le c cc
  rw [hb] at wb
  rw [hd] at wd
  rw [hc] at wc
  have hbound := linear_bound B tail.length b d c hB wb wd wc
  have hvolume : (first::tail).flatten.length = B+tail.length*B := by
    rw [List.flatten_cons,List.length_append,hf,BlockRotationData.uniform_volume B tail hu]
  rw [← hvolume] at hbound
  exact (negate_hoare source dest scratch p q r first tail B hf hu b d c hb hd hc hblank).consequence
    (fun _ h => h) (fun _ h => h) hbound

end IntegerMultBounds.Machine.BlockNegationReuse

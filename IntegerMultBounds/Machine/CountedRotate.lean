import IntegerMultBounds.Machine.CountedSeek
import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.BlockRotationData

/-! Literal cyclic rotation of a raw block using three immutable binary
length descriptors. Skip the prefix, copy the suffix, rewind over the complete
block, then copy the prefix. Every seek, clock reset, and join is charged.
Descriptor synthesis is explicit caller work, not an assumed free operation. -/

namespace IntegerMultBounds.Machine.CountedRotate

open CountedCopyReuse (empty binary)

/-- Source, destination, reusable clock, prefix/suffix/total descriptors. -/
def bank (source dest : ℤ → Fin 4) (prefixBits suffixBits totalBits : List Bool) (p q : ℤ) : Tapes 6 0 where
  head := ![p,q,1,1,1,1]
  tape := ![source,dest,empty,binary prefixBits,binary suffixBits,binary totalBits]

def seekPrefixSlots : Fin (3+3) ≃ Fin 6 :=
  (Equiv.swap 2 3).trans (Equiv.swap 1 2)

def seekTotalSlots : Fin (3+3) ≃ Fin 6 := seekPrefixSlots.trans (Equiv.swap 3 5)

def copySuffixSlots : Fin (4+2) ≃ Fin 6 := Equiv.swap 3 4

def copyPrefixSlots : Fin (4+2) ≃ Fin 6 := Equiv.refl _

def seekPrefix : Program 6 16 0 := Placement.placed (u := 3) CountedSeek.program seekPrefixSlots

def copySuffix : Program 6 16 0 := Placement.placed (u := 2) CountedCopyReuse.program copySuffixSlots

def seekTotal : Program 6 16 0 := Placement.placed (u := 3) CountedSeek.backwardProgram seekTotalSlots

def copyPrefix : Program 6 16 0 := Placement.placed (u := 2) CountedCopyReuse.program copyPrefixSlots

def program : Program 6 64 0 := seq (seq (seq seekPrefix copySuffix) seekTotal) copyPrefix

private theorem active_seek_prefix (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    Placement.active (s := 3) seekPrefixSlots (bank f g b c d p q) = CountedSeek.bank f p b := by
  unfold Placement.active bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem active_seek_total (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    Placement.active (s := 3) seekTotalSlots (bank f g b c d p q) = CountedSeek.bank f p d := by
  unfold Placement.active bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem active_copy_suffix (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    Placement.active (s := 4) copySuffixSlots (bank f g b c d p q) =
      CountedCopyReuse.bank f g empty (binary c) p q 1 1 := by
  unfold Placement.active bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem active_copy_prefix (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    Placement.active (s := 4) copyPrefixSlots (bank f g b c d p q) =
      CountedCopyReuse.bank f g empty (binary b) p q 1 1 := by
  unfold Placement.active bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_seek_prefix (f g f' : ℤ → Fin 4) (b c d : List Bool) (p q p' : ℤ) :
    Placement.replace (s := 3) seekPrefixSlots (bank f g b c d p q) (CountedSeek.bank f' p' b) =
      bank f' g b c d p' q := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_seek_total (f g f' : ℤ → Fin 4) (b c d : List Bool) (p q p' : ℤ) :
    Placement.replace (s := 3) seekTotalSlots (bank f g b c d p q) (CountedSeek.bank f' p' d) =
      bank f' g b c d p' q := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_copy_suffix (f g f' g' : ℤ → Fin 4) (b c d : List Bool) (p q p' q' : ℤ) :
    Placement.replace (s := 4) copySuffixSlots (bank f g b c d p q)
      (CountedCopyReuse.bank f' g' empty (binary c) p' q' 1 1) = bank f' g' b c d p' q' := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_copy_prefix (f g f' g' : ℤ → Fin 4) (b c d : List Bool) (p q p' q' : ℤ) :
    Placement.replace (s := 4) copyPrefixSlots (bank f g b c d p q)
      (CountedCopyReuse.bank f' g' empty (binary b) p' q' 1 1) = bank f' g' b c d p' q' := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem seek_prefix_hoare (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    HoareTime seekPrefix (fun v => v = bank f g b c d p q)
      (fun v => v = bank f g b c d (p+Counter.value b) q)
      (5*Counter.value b+7*b.length+16) := by
  have h := Placement.hoare_at (CountedSeek.seek_hoare f p b) seekPrefixSlots
    (bank f g b c d p q) (active_seek_prefix f g b c d p q)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_seek_prefix f g f b c d p q _

private theorem seek_total_hoare (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    HoareTime seekTotal (fun v => v = bank f g b c d p q)
      (fun v => v = bank f g b c d (p-Counter.value d) q)
      (5*Counter.value d+7*d.length+16) := by
  have h := Placement.hoare_at (CountedSeek.seek_backward_hoare f p d) seekTotalSlots
    (bank f g b c d p q) (active_seek_total f g b c d p q)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_seek_total f g f b c d p q _

private theorem copy_suffix_hoare (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ)
    (xs : List (Fin 4)) (hc : Counter.value c = xs.length) :
    HoareTime copySuffix (fun v => v = bank (putWord f p xs) g b c d p q)
      (fun v => v = bank (putWord f p xs) (putWord g q xs) b c d (p+xs.length) (q+xs.length))
      (5*xs.length+7*c.length+16) := by
  have h := Placement.hoare_at (CountedCopyReuse.copy_hoare f g p q xs c hc) copySuffixSlots
    (bank (putWord f p xs) g b c d p q) (active_copy_suffix _ _ _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_copy_suffix _ _ _ _ _ _ _ _ _ _ _

private theorem copy_prefix_hoare (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ)
    (xs : List (Fin 4)) (hb : Counter.value b = xs.length) :
    HoareTime copyPrefix (fun v => v = bank (putWord f p xs) g b c d p q)
      (fun v => v = bank (putWord f p xs) (putWord g q xs) b c d (p+xs.length) (q+xs.length))
      (5*xs.length+7*b.length+16) := by
  have h := Placement.hoare_at (CountedCopyReuse.copy_hoare f g p q xs b hb) copyPrefixSlots
    (bank (putWord f p xs) g b c d p q) (active_copy_prefix _ _ _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_copy_prefix _ _ _ _ _ _ _ _ _ _ _

/-- Complete literal rotation of a raw prefix/suffix split. All three descriptors
are retained and the work clock returns empty. Empty pieces are allowed. -/
theorem rotate_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs ys : List (Fin 4))
    (b c d : List Bool) (hb : Counter.value b = xs.length) (hc : Counter.value c = ys.length)
    (hd : Counter.value d = xs.length+ys.length) :
    HoareTime program
      (fun v => v = bank (putWord source p (xs++ys)) dest b c d p q)
      (fun v => v = bank (putWord source p (xs++ys)) (putWord dest q (ys++xs)) b c d
        (p+xs.length) (q+ys.length+xs.length))
      (15*xs.length+10*ys.length+14*b.length+7*c.length+7*d.length+67) := by
  have h₀ := seek_prefix_hoare (putWord source p (xs++ys)) dest b c d p q
  rw [hb] at h₀
  have h₁ := copy_suffix_hoare (putWord source p xs) dest b c d (p+xs.length) q ys hc
  rw [putWord_append_forward] at h₁
  have h₂ := seek_total_hoare (putWord source p (xs++ys)) (putWord dest q ys) b c d
    (p+xs.length+ys.length) (q+ys.length)
  rw [hd] at h₂
  have hpos : p+(xs.length : ℤ)+ys.length-(xs.length+ys.length : ℕ) = p := by omega
  rw [hpos] at h₂
  have h₃ := copy_prefix_hoare (putWord source (p+xs.length) ys) (putWord dest q ys) b c d
    p (q+ys.length) xs hb
  rw [← putWord_append,putWord_append_forward] at h₃
  have h := ((h₀.seq h₁).seq h₂).seq h₃
  apply h.consequence (fun _ hv => hv) (fun _ hv => hv)
  omega

/-- A complete single-fiber controlled shift. The caller supplies binary
piece-length descriptors; the literal machine performs the payload movement
and restores every control tape within linear payload time plus descriptor size. -/
theorem block_shift_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (blocks : List (List (Fin 4))) (B a : ℕ) (hu : BlockRotationData.Uniform B blocks)
    (ha : a < blocks.length) (b c d : List Bool)
    (hb : Counter.value b = (blocks.length-a)*B) (hc : Counter.value c = a*B)
    (hd : Counter.value d = blocks.length*B) :
    HoareTime program
      (fun v => v = bank (putWord source p blocks.flatten) dest b c d p q)
      (fun v => v = bank (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate a blocks).flatten) b c d
        (p+(((blocks.length-a)*B : ℕ) : ℤ)) (q+((blocks.length*B : ℕ) : ℤ)))
      (15*(blocks.length*B)+14*b.length+7*c.length+7*d.length+67) := by
  have hvol := BlockRotationData.uniform_volume B blocks hu
  have hsum : (blocks.length-a)*B+a*B = blocks.length*B := by
    rw [← Nat.add_mul,Nat.sub_add_cancel ha.le]
  have htake : (blocks.flatten.take ((blocks.length-a)*B)).length = (blocks.length-a)*B := by
    rw [List.length_take,hvol,Nat.min_eq_left (by omega)]
  have hdrop : (blocks.flatten.drop ((blocks.length-a)*B)).length = a*B := by
    rw [List.length_drop,hvol]
    omega
  have h := rotate_hoare source dest p q (blocks.flatten.take ((blocks.length-a)*B))
    (blocks.flatten.drop ((blocks.length-a)*B)) b c d
    (by simpa only [htake] using hb) (by simpa only [hdrop] using hc)
    (by simpa only [htake,hdrop,hsum] using hd)
  have hout : blocks.flatten.drop ((blocks.length-a)*B) ++
      blocks.flatten.take ((blocks.length-a)*B) = (BlockRotationData.rotate a blocks).flatten := by
    simpa only [Nat.mod_eq_of_lt ha] using (BlockRotationData.rotated_payload_split a B blocks hu).symm
  rw [List.take_append_drop,hout,htake,hdrop] at h
  have hhead : q+((a*B : ℕ) : ℤ)+(((blocks.length-a)*B : ℕ) : ℤ) = q+((blocks.length*B : ℕ) : ℤ) := by
    omega
  rw [hhead] at h
  apply h.consequence (fun _ hv => hv) (fun _ hv => hv)
  omega

end IntegerMultBounds.Machine.CountedRotate

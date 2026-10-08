import IntegerMultBounds.Machine.CountedRotate

/-! A cyclic raw-block rotation whose source and destination both finish at the
next block. This adds a real counted seek over the final suffix to the proved
rotation; descriptor resets and the extra sequential join are charged. -/

namespace IntegerMultBounds.Machine.CountedRotateAdvance

open CountedRotate (bank)

def suffixSlots : Fin (3+3) ≃ Fin 6 :=
  CountedRotate.seekPrefixSlots.trans (Equiv.swap 3 4)

def seekSuffix : Program 6 16 0 := Placement.placed (u := 3) CountedSeek.program suffixSlots

def program : Program 6 80 0 := seq CountedRotate.program seekSuffix

private theorem active_suffix (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    Placement.active (s := 3) suffixSlots (bank f g b c d p q) = CountedSeek.bank f p c := by
  unfold Placement.active bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_suffix (f g f' : ℤ → Fin 4) (b c d : List Bool) (p q p' : ℤ) :
    Placement.replace (s := 3) suffixSlots (bank f g b c d p q) (CountedSeek.bank f' p' c) =
      bank f' g b c d p' q := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem seek_suffix_hoare (f g : ℤ → Fin 4) (b c d : List Bool) (p q : ℤ) :
    HoareTime seekSuffix (fun v => v = bank f g b c d p q)
      (fun v => v = bank f g b c d (p+Counter.value c) q)
      (5*Counter.value c+7*c.length+16) := by
  have h := Placement.hoare_at (CountedSeek.seek_hoare f p c) suffixSlots
    (bank f g b c d p q) (active_suffix f g b c d p q)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_suffix f g f b c d p q _

/-- Every bit is rotated and both payload heads advance the complete block.
All descriptor tapes survive and the reusable inner clock is empty again. -/
theorem rotate_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs ys : List (Fin 4))
    (b c d : List Bool) (hb : Counter.value b = xs.length) (hc : Counter.value c = ys.length)
    (hd : Counter.value d = xs.length+ys.length) :
    HoareTime program
      (fun v => v = bank (putWord source p (xs++ys)) dest b c d p q)
      (fun v => v = bank (putWord source p (xs++ys)) (putWord dest q (ys++xs)) b c d
        (p+(xs.length+ys.length : ℕ)) (q+(xs.length+ys.length : ℕ)))
      (15*(xs.length+ys.length)+14*b.length+14*c.length+7*d.length+84) := by
  have h₀ := CountedRotate.rotate_hoare source dest p q xs ys b c d hb hc hd
  have h₁ := seek_suffix_hoare (putWord source p (xs++ys)) (putWord dest q (ys++xs)) b c d
    (p+xs.length) (q+ys.length+xs.length)
  rw [hc] at h₁
  have h := h₀.seq h₁
  apply h.consequence (fun _ hv => hv)
  · intro v hv
    simpa only [Nat.cast_add,add_assoc,add_comm,add_left_comm] using hv
  · omega

end IntegerMultBounds.Machine.CountedRotateAdvance

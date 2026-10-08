import IntegerMultBounds.Machine.CountedSpanSeek
import IntegerMultBounds.Machine.ScratchReset

/-! Restore a complete intermediate fiber using only block-width and block-count
descriptors. Every rewind, erase transition and clock operation is charged. -/
namespace IntegerMultBounds.Machine.CountedSpanReset

open CountedCopyReuse (empty binary)
abbrev bank := CountedSpanSeek.bank

private theorem erased_append (f : ℤ → Fin 4) (p : ℤ) (m n : ℕ) :
    CountedErase.erased (CountedErase.erased f p m) (p+m) n = CountedErase.erased f p (m+n) := by
  funext z
  simp only [CountedErase.erased]
  split_ifs <;> try rfl
  all_goals omega

def eraseProgram : Program 5 34 0 := CountedLoopReuse.program CountedErase.program

def eraseBound (B n : ℕ) (bs ns : List Bool) : ℕ :=
  n*(7*B+7*bs.length+22)+7*ns.length+16

theorem erase_hoare (f : ℤ → Fin 4) (p : ℤ) (B n : ℕ) (bs ns : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) :
    HoareTime eraseProgram (fun v => v = bank f p bs ns)
      (fun v => v = bank (CountedErase.erased f p (n*B)) (p+((n*B : ℕ) : ℤ)) bs ns)
      (eraseBound B n bs ns) := by
  let v := fun i : ℕ => CountedErase.bank (CountedErase.erased f p (i*B)) (p+((i*B : ℕ) : ℤ)) bs
  have hh : ∀ i < n, HoareTime CountedErase.program (fun w => w = v i)
      (fun w => w = v (i+1)) (7*B+7*bs.length+16) := by
    intro i _
    have h := CountedErase.erase_hoare (CountedErase.erased f p (i*B)) (p+((i*B : ℕ) : ℤ)) bs
    rw [hb,erased_append] at h
    have he : i*B+B = (i+1)*B := by ring
    have hp : p+((i*B : ℕ) : ℤ)+(B : ℤ) = p+(((i+1)*B : ℕ) : ℤ) := by push_cast; ring
    simpa only [v,he,hp] using h
  have h := CountedLoopReuse.loop_hoare CountedErase.program ns n v
    (fun _ => 7*B+7*bs.length+16) hn hh
  apply h.consequence
  · intro w hw
    simpa only [v,bank,CountedSpanSeek.bank,zero_mul,Nat.cast_zero,add_zero,
      CountedErase.erased_zero,ScratchReset.erase_bank] using hw
  · intro w hw
    simpa only [v,bank,CountedSpanSeek.bank,ScratchReset.erase_bank] using hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,eraseBound]
    nlinarith

def program : Program 5 98 0 :=
  seq (seq CountedSpanSeek.backwardProgram eraseProgram) CountedSpanSeek.backwardProgram

def bound (B n : ℕ) (bs ns : List Bool) : ℕ :=
  n*(17*B+21*bs.length+66)+21*ns.length+50

theorem reset_hoare (f : ℤ → Fin 4) (p : ℤ) (B n : ℕ) (bs ns : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) :
    HoareTime program (fun v => v = bank f (p+((n*B : ℕ) : ℤ)) bs ns)
      (fun v => v = bank (CountedErase.erased f p (n*B)) p bs ns) (bound B n bs ns) := by
  have h₀ := CountedSpanSeek.seek_backward_hoare f (p+((n*B : ℕ) : ℤ)) B n bs ns hb hn
  rw [add_sub_cancel_right] at h₀
  have h₁ := erase_hoare f p B n bs ns hb hn
  have h₂ := CountedSpanSeek.seek_backward_hoare (CountedErase.erased f p (n*B))
    (p+((n*B : ℕ) : ℤ)) B n bs ns hb hn
  rw [add_sub_cancel_right] at h₂
  apply ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h)
  dsimp only [CountedSpanSeek.bound,eraseBound,bound]
  nlinarith

theorem linear_bound (B n : ℕ) (bs ns : List Bool) (hB : 0 < B)
    (hb : bs.length ≤ B+1) (hn : ns.length ≤ n+1) :
    bound B n bs ns ≤ 146*(n*B)+71 := by
  have h : 17*B+21*bs.length+66 ≤ 125*B := by omega
  have hm := Nat.mul_le_mul_left n h
  have hnB : n ≤ n*B := by nlinarith
  dsimp only [bound]
  nlinarith

theorem reset_word_hoare_linear (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (B n : ℕ) (bs ns : List Bool) (hlen : xs.length = n*B)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    HoareTime program (fun v => v = bank (putWord f p xs) (p+xs.length) bs ns)
      (fun v => v = bank f p bs ns) (146*xs.length+71) := by
  have h := reset_hoare (putWord f p xs) p B n bs ns hb hn
  rw [← hlen,CountedErase.erased_word f p xs hblank] at h
  have wb := GrowingCounterData.canonical_width bs cb
  have wn := GrowingCounterData.canonical_width ns cn
  have lb := Nat.log2_le_self (Counter.value bs)
  have ln := Nat.log2_le_self (Counter.value ns)
  have ht := linear_bound B n bs ns hB (by omega) (by omega)
  rw [← hlen] at ht
  exact h.consequence (fun _ h => h) (fun _ h => h) ht

end IntegerMultBounds.Machine.CountedSpanReset

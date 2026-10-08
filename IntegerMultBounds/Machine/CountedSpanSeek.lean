import IntegerMultBounds.Machine.CountedSeek
import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! Reposition a complete uniform fiber using only its block-width and count
descriptors. This physically moves the payload head and restores both clocks;
no separately prepared product-length descriptor is needed. -/
namespace IntegerMultBounds.Machine.CountedSpanSeek

open CountedCopyReuse (empty binary)

def bank (f : ℤ → Fin 4) (p : ℤ) (bs ns : List Bool) : Tapes 5 0 :=
  CountedLoopReuse.bank (CountedSeek.bank f p bs) empty (binary ns) 1 1

def program : Program 5 32 0 := CountedLoopReuse.program CountedSeek.program

def backwardProgram : Program 5 32 0 := CountedLoopReuse.program CountedSeek.backwardProgram

def bound (B n : ℕ) (bs ns : List Bool) : ℕ :=
  n*(5*B+7*bs.length+22)+7*ns.length+16

theorem seek_hoare (f : ℤ → Fin 4) (p : ℤ) (B n : ℕ) (bs ns : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) :
    HoareTime program (fun v => v = bank f p bs ns)
      (fun v => v = bank f (p+((n*B : ℕ) : ℤ)) bs ns) (bound B n bs ns) := by
  let v := fun i : ℕ => CountedSeek.bank f (p+((i*B : ℕ) : ℤ)) bs
  have hh : ∀ i < n, HoareTime CountedSeek.program (fun w => w = v i)
      (fun w => w = v (i+1)) (5*B+7*bs.length+16) := by
    intro i _
    have h := CountedSeek.seek_hoare f (p+((i*B : ℕ) : ℤ)) bs
    rw [hb] at h
    have he : p+((i*B : ℕ) : ℤ)+(B : ℤ) = p+(((i+1)*B : ℕ) : ℤ) := by push_cast; ring
    simpa only [v,he] using h
  have h := CountedLoopReuse.loop_hoare CountedSeek.program ns n v
    (fun _ => 5*B+7*bs.length+16) hn hh
  apply h.consequence
  · intro w hw; simpa only [v,bank,zero_mul,Nat.cast_zero,add_zero] using hw
  · intro w hw; exact hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,bound]
    nlinarith

theorem seek_backward_hoare (f : ℤ → Fin 4) (p : ℤ) (B n : ℕ) (bs ns : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) :
    HoareTime backwardProgram (fun v => v = bank f p bs ns)
      (fun v => v = bank f (p-((n*B : ℕ) : ℤ)) bs ns) (bound B n bs ns) := by
  let v := fun i : ℕ => CountedSeek.bank f (p-((i*B : ℕ) : ℤ)) bs
  have hh : ∀ i < n, HoareTime CountedSeek.backwardProgram (fun w => w = v i)
      (fun w => w = v (i+1)) (5*B+7*bs.length+16) := by
    intro i _
    have h := CountedSeek.seek_backward_hoare f (p-((i*B : ℕ) : ℤ)) bs
    rw [hb] at h
    have he : p-((i*B : ℕ) : ℤ)-(B : ℤ) = p-(((i+1)*B : ℕ) : ℤ) := by push_cast; ring
    simpa only [v,he] using h
  have h := CountedLoopReuse.loop_hoare CountedSeek.backwardProgram ns n v
    (fun _ => 5*B+7*bs.length+16) hn hh
  apply h.consequence
  · intro w hw; simpa only [v,bank,zero_mul,Nat.cast_zero,sub_zero] using hw
  · intro w hw; exact hw
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,bound]
    nlinarith

theorem linear_bound (B n : ℕ) (bs ns : List Bool) (hB : 0 < B)
    (hb : bs.length ≤ B+1) (hn : ns.length ≤ n+1) :
    bound B n bs ns ≤ 48*(n*B)+23 := by
  have hh : 5*B+7*bs.length+22 ≤ 41*B := by omega
  have hm := Nat.mul_le_mul_left n hh
  have hnB : n ≤ n*B := by nlinarith
  dsimp only [bound]
  nlinarith

theorem rewind_hoare_linear (f : ℤ → Fin 4) (p : ℤ) (B n : ℕ) (bs ns : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value ns = n) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime backwardProgram (fun v => v = bank f (p+((n*B : ℕ) : ℤ)) bs ns)
      (fun v => v = bank f p bs ns) (48*(n*B)+23) := by
  have wb := GrowingCounterData.canonical_width bs cb
  have wn := GrowingCounterData.canonical_width ns cn
  have lb := Nat.log2_le_self (Counter.value bs)
  have ln := Nat.log2_le_self (Counter.value ns)
  have h := seek_backward_hoare f (p+((n*B : ℕ) : ℤ)) B n bs ns hb hn
  rw [add_sub_cancel_right] at h
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (linear_bound B n bs ns hB (by omega) (by omega))

end IntegerMultBounds.Machine.CountedSpanSeek

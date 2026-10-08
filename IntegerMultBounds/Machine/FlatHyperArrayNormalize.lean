import IntegerMultBounds.Machine.CountedHyperVolumeLoop
import IntegerMultBounds.Machine.FlatArrayNormalize

/-! Four-dimensional physical payload normalization, using the four existing
count descriptors and restoring all four clocks. -/
namespace IntegerMultBounds.Machine.FlatHyperArrayNormalize
open FlatArrayNormalize
variable {a : ℕ}

def bank (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs qs cs ns : List Bool) : Tapes 10 a :=
  CountedHyperVolumeLoop.bank (pair f g p q) bs qs cs ns

def rewindProgram : Program 10 66 a := CountedHyperVolumeLoop.program backCell
def moveProgram : Program 10 66 a := CountedHyperVolumeLoop.program moveCell

theorem rewind_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (N C Q B : ℕ) (bs qs cs ns : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hc : Counter.value cs = C) (hn : Counter.value ns = N) :
    HoareTime rewindProgram (fun v => v = bank f g (p+((N*(C*(Q*B)) : ℕ) : ℤ)) (q+((N*(C*(Q*B)) : ℕ) : ℤ)) bs qs cs ns)
      (fun v => v = bank f g p q bs qs cs ns) (CountedHyperVolumeLoop.bound 1 N C Q B bs qs cs ns) := by
  have hh := CountedHyperVolumeLoop.loop_hoare backCell N C Q B 1 bs qs cs ns hb hq hc hn
    (fun i => pair f g (p+((N*(C*(Q*B)) : ℕ) : ℤ)-i) (q+((N*(C*(Q*B)) : ℕ) : ℤ)-i))
    (by intro i hi
        have h := back_cell_hoare f g (p+((N*(C*(Q*B)) : ℕ) : ℤ)-i) (q+((N*(C*(Q*B)) : ℕ) : ℤ)-i)
        have he (z : ℤ) : z-i-1 = z-((i+1 : ℕ) : ℤ) := by omega
        simpa only [he] using h)
  simpa only [rewindProgram,bank,Nat.cast_zero,sub_zero,add_sub_cancel_right] using hh

private theorem write_take (g : ℤ → Fin (a+4)) (q : ℤ) (xs : List (Fin (a+4))) (i : ℕ) (hi : i < xs.length) :
    Function.update (putWord g q (xs.take i)) (q+i) xs[i] = putWord g q (xs.take (i+1)) := by
  have hl : (xs.take i).length = i := List.length_take_of_le (by omega)
  have hh := putWord_append_forward g q (xs.take i) [xs[i]]
  simpa only [putWord,hl,List.take_succ_eq_append_getElem hi] using hh

theorem move_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (xs : List (Fin (a+4)))
    (N C Q B : ℕ) (bs qs cs ns : List Bool) (hlen : xs.length = N*(C*(Q*B)))
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hc : Counter.value cs = C) (hn : Counter.value ns = N) :
    HoareTime moveProgram (fun v => v = bank (putWord f p xs) g p q bs qs cs ns)
      (fun v => v = bank (erased (putWord f p xs) p xs.length) (putWord g q xs)
        (p+xs.length) (q+xs.length) bs qs cs ns) (CountedHyperVolumeLoop.bound 1 N C Q B bs qs cs ns) := by
  let v := fun i => pair (erased (putWord f p xs) p i) (putWord g q (xs.take i)) (p+i) (q+i)
  have hh := CountedHyperVolumeLoop.loop_hoare moveCell N C Q B 1 bs qs cs ns hb hq hc hn v
    (by intro i hi
        have hi' : i < xs.length := by omega
        have hread : erased (putWord f p xs) p i (p+i) = xs[i] := by
          simp only [erased,lt_self_iff_false,and_false,ite_false]
          exact WordSegments.get f p xs i hi'
        have h := move_cell_hoare (erased (putWord f p xs) p i) (putWord g q (xs.take i)) (p+i) (q+i)
        rw [erased_succ,hread,write_take g q xs i hi'] at h
        simpa only [v,Nat.cast_add,Nat.cast_one,add_assoc] using h)
  simpa only [moveProgram,bank,v,Nat.cast_zero,add_zero,erased_zero,List.take_zero,putWord,
    ← hlen,List.take_length] using hh

/-- Whole normalization is a fixed three-pass machine. -/
def program : Program 10 198 a := seq (seq rewindProgram moveProgram) rewindProgram

/-- After normalization, the old output is blank again and the common input
contains the new flat word, with both heads at their actual origins. -/
theorem normalize_hoare (scratch common : ℤ → Fin (a+4)) (p q : ℤ) (xs : List (Fin (a+4)))
    (N C Q B : ℕ) (bs qs cs ns : List Bool) (hlen : xs.length = N*(C*(Q*B)))
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hc : Counter.value cs = C) (hn : Counter.value ns = N)
    (hN : 0 < N) (hC : 0 < C) (hQ : 0 < Q) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → scratch z = blank) :
    HoareTime program
      (fun v => v = bank (putWord scratch p xs) common (p+xs.length) (q+xs.length) bs qs cs ns)
      (fun v => v = bank scratch (putWord common q xs) p q bs qs cs ns)
      (435*xs.length+2) := by
  have h₀ := rewind_hoare (putWord scratch p xs) common p q N C Q B bs qs cs ns hb hq hc hn
  have h₁ := move_hoare scratch common p q xs N C Q B bs qs cs ns hlen hb hq hc hn
  rw [erased_word scratch p xs hblank] at h₁
  have h₂ := rewind_hoare scratch (putWord common q xs) p q N C Q B bs qs cs ns hb hq hc hn
  rw [← hlen] at h₀ h₂
  apply ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) _
  have hbound := CountedHyperVolumeLoop.bound_linear N C Q B bs qs cs ns hN hC hQ hB hb hq hc hn cb cq cc cn
  rw [← hlen] at hbound
  omega

end IntegerMultBounds.Machine.FlatHyperArrayNormalize

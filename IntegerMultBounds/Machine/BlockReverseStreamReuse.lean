import IntegerMultBounds.Machine.BlockReverseStream
import IntegerMultBounds.Machine.CountedLoopReuse

/-! Reusable blockwise payload reversal. The outer count descriptor remains
immutable, its mutable clock is prepared and fully cleared by the actual
machine, and the advancing block body preserves its own reusable controls. -/

namespace IntegerMultBounds.Machine.BlockReverseStreamReuse

open BlockReverseAdvance (bank)
open BlockReverseStream (state outputPrefix bodyBound body_hoare)

/-- Six fixed tapes and fixed control, independently of block width and count. -/
def program : Program 6 68 0 := CountedLoopReuse.program BlockReverseAdvance.program

/-- Both descriptor banks are retained, both work clocks are clean, and all
four control heads finish at one. Raw payload heads advance by the full volume. -/
theorem reverse_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (hu : BlockRotationData.Uniform B blocks) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = blocks.length) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p blocks.flatten) dest bs p q)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p blocks.flatten) (putWord dest q (blocks.map List.reverse).flatten) bs
          (p+((blocks.length*B : ℕ) : ℤ)) (q+((blocks.length*B : ℕ) : ℤ)))
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (blocks.length*(bodyBound B bs+6)+7*countBits.length+16) := by
  have h := CountedLoopReuse.loop_hoare BlockReverseAdvance.program countBits blocks.length
    (state source dest p q blocks B bs) (fun _ => bodyBound B bs) hn
    (body_hoare source dest p q blocks B hu bs hb)
  have hcost : (∑ _i ∈ Finset.range blocks.length, bodyBound B bs)+6*blocks.length+
      7*countBits.length+16 = blocks.length*(bodyBound B bs+6)+7*countBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at h
  simpa only [program,state,outputPrefix,List.take_zero,List.map_nil,List.flatten_nil,
    putWord,zero_mul,Nat.cast_zero,add_zero,List.take_length] using h

/-- Linear-volume accounting includes the actual outer preparation and cleanup. -/
theorem linear_bound (B n : ℕ) (bs countBits : List Bool) (hB : 1 ≤ B)
    (hb : bs.length ≤ B+1) (hn : countBits.length ≤ n+1) :
    n*(bodyBound B bs+6)+7*countBits.length+16 ≤ 124*(n*B)+23 := by
  have hbody : bodyBound B bs+6 ≤ 117*B := by
    dsimp only [bodyBound]
    omega
  have hh := Nat.mul_le_mul_left n hbody
  have hnB : n ≤ n*B := by nlinarith
  nlinarith

private theorem canonical_width_le (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs+1 := by
  have hw := GrowingCounterData.canonical_width bs h
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

/-- Canonical immutable descriptors give a complete linear-time raw-stream
routine with reusable state, rather than leaving an exhausted outer clock. -/
theorem reverse_hoare_linear (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (hu : BlockRotationData.Uniform B blocks) (hB : 1 ≤ B) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = blocks.length)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p blocks.flatten) dest bs p q)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p blocks.flatten) (putWord dest q (blocks.map List.reverse).flatten) bs
          (p+((blocks.length*B : ℕ) : ℤ)) (q+((blocks.length*B : ℕ) : ℤ)))
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (124*blocks.flatten.length+23) := by
  have wb := canonical_width_le bs cb
  have wn := canonical_width_le countBits cn
  rw [hb] at wb
  rw [hn] at wn
  have hbound := linear_bound B blocks.length bs countBits hB wb wn
  rw [← BlockRotationData.uniform_volume B blocks hu] at hbound
  exact (reverse_hoare source dest p q blocks B hu bs countBits hb hn).consequence
    (fun _ h => h) (fun _ h => h) hbound

end IntegerMultBounds.Machine.BlockReverseStreamReuse

import IntegerMultBounds.Machine.BlockReverseAdvance
import IntegerMultBounds.Machine.FiberShift

/-! One fixed counted machine reverses the payload inside each equal-width
block, preserving the order of the blocks themselves. The body restores its
immutable width descriptor and local clock after every block; a separate outer
clock controls termination without rescanning a count descriptor per block. -/

namespace IntegerMultBounds.Machine.BlockReverseStream

open BlockReverseAdvance (bank)
variable {α : Type*}

def outputPrefix (i : ℕ) (blocks : List (List α)) : List α :=
  ((blocks.take i).map List.reverse).flatten

theorem prefix_succ (i : ℕ) (blocks : List (List α)) (hi : i < blocks.length) :
    outputPrefix (i+1) blocks = outputPrefix i blocks ++ blocks[i].reverse := by
  simp only [outputPrefix,List.take_succ_eq_append_getElem hi,List.map_append,List.flatten_append,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]

theorem prefix_length (i B : ℕ) (blocks : List (List α))
    (hu : BlockRotationData.Uniform B blocks) (hi : i ≤ blocks.length) :
    (outputPrefix i blocks).length = i*B := by
  have hh : BlockRotationData.Uniform B ((blocks.take i).map List.reverse) := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    simpa only [List.length_reverse] using hu ys (List.mem_of_mem_take hy)
  rw [outputPrefix,BlockRotationData.uniform_volume B _ hh,List.length_map,List.length_take,
    Nat.min_eq_left hi]

/-- The source tape is fixed while output grows at successive physical block
positions. Neither payload head revisits any completed block in this invariant. -/
def state (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (bs : List Bool) (i : ℕ) : Tapes 4 0 :=
  bank (putWord source p blocks.flatten) (putWord dest q (outputPrefix i blocks)) bs
    (p+((i*B : ℕ) : ℤ)) (q+((i*B : ℕ) : ℤ))

def bodyBound (B : ℕ) (bs : List Bool) : ℕ := 15*B+21*bs.length+54

/-- The literal advancing reverse routine processes the next complete block
and retains all previously written output and every source cell. -/
theorem body_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (hu : BlockRotationData.Uniform B blocks) (bs : List Bool)
    (hb : Counter.value bs = B) (i : ℕ) (hi : i < blocks.length) :
    HoareTime BlockReverseAdvance.program
      (fun v => v = state source dest p q blocks B bs i)
      (fun v => v = state source dest p q blocks B bs (i+1))
      (bodyBound B bs) := by
  have hrow : blocks[i].length = B := hu _ (List.getElem_mem hi)
  have h := BlockReverseAdvance.reverse_hoare (putWord source p blocks.flatten)
    (putWord dest q (outputPrefix i blocks)) (p+((i*B : ℕ) : ℤ)) (q+((i*B : ℕ) : ℤ))
    blocks[i] bs (by simpa only [hrow] using hb)
  rw [FiberShift.source_fiber source p blocks B i hu hi,hrow] at h
  have hout : putWord (putWord dest q (outputPrefix i blocks)) (q+((i*B : ℕ) : ℤ)) blocks[i].reverse =
      putWord dest q (outputPrefix (i+1) blocks) := by
    rw [← prefix_length i B blocks hu hi.le,putWord_append_forward,prefix_succ i blocks hi]
  rw [hout] at h
  have hlen : (i+1)*B = i*B+B := by ring
  simpa only [state,bodyBound,hlen,Nat.cast_add,add_assoc] using h

/-- One fixed five-tape machine, independent of the block width and count. -/
def program : Program 5 57 0 := CountedLoop.program BlockReverseAdvance.program

/-- Complete blockwise reversal on raw streams. The immutable B descriptor and
inner clock survive every body call; the outer mutable count ends all ones at
its original least-significant position. Descriptor preparation is explicit. -/
theorem reverse_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (hu : BlockRotationData.Uniform B blocks) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = blocks.length) :
    HoareTime program
      (fun v => v = CountedLoop.bank
        (bank (putWord source p blocks.flatten) dest bs p q) CountedCopyReuse.empty countBits)
      (fun v => v = CountedLoop.bank
        (bank (putWord source p blocks.flatten) (putWord dest q (blocks.map List.reverse).flatten) bs
          (p+((blocks.length*B : ℕ) : ℤ)) (q+((blocks.length*B : ℕ) : ℤ))) CountedCopyReuse.empty
        (List.replicate countBits.length true))
      (blocks.length*(bodyBound B bs+6)+2*countBits.length+2) := by
  have h := CountedLoop.loop_hoare BlockReverseAdvance.program CountedCopyReuse.empty countBits
    blocks.length (state source dest p q blocks B bs) (fun _ => bodyBound B bs)
    hn (by simp [CountedCopyReuse.empty])
    (by simp [CountedCopyReuse.empty,show (1 : ℤ)+countBits.length ≠ 0 by omega])
    (body_hoare source dest p q blocks B hu bs hb)
  have hcost : (∑ _i ∈ Finset.range blocks.length, bodyBound B bs)+6*blocks.length+
      2*countBits.length+2 = blocks.length*(bodyBound B bs+6)+2*countBits.length+2 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at h
  simpa only [program,state,outputPrefix,List.take_zero,List.map_nil,List.flatten_nil,
    putWord,zero_mul,Nat.cast_zero,add_zero,List.take_length] using h

/-- Uniform linear payload-volume bound when blocks are nonempty and descriptor
widths satisfy their elementary canonical bounds. -/
theorem linear_bound (B n : ℕ) (bs countBits : List Bool) (hB : 1 ≤ B)
    (hb : bs.length ≤ B+1) (hn : countBits.length ≤ n+1) :
    n*(bodyBound B bs+6)+2*countBits.length+2 ≤ 119*(n*B)+4 := by
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

/-- Canonical prepared descriptors give a genuine linear-volume bound for the
complete machine, including clock scans, body cleanup and every head movement. -/
theorem reverse_hoare_linear (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (B : ℕ) (hu : BlockRotationData.Uniform B blocks) (hB : 1 ≤ B) (bs countBits : List Bool)
    (hb : Counter.value bs = B) (hn : Counter.value countBits = blocks.length)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime program
      (fun v => v = CountedLoop.bank
        (bank (putWord source p blocks.flatten) dest bs p q) CountedCopyReuse.empty countBits)
      (fun v => v = CountedLoop.bank
        (bank (putWord source p blocks.flatten) (putWord dest q (blocks.map List.reverse).flatten) bs
          (p+((blocks.length*B : ℕ) : ℤ)) (q+((blocks.length*B : ℕ) : ℤ))) CountedCopyReuse.empty
        (List.replicate countBits.length true)) (119*blocks.flatten.length+4) := by
  have wb := canonical_width_le bs cb
  have wn := canonical_width_le countBits cn
  rw [hb] at wb
  rw [hn] at wn
  have hbound := linear_bound B blocks.length bs countBits hB wb wn
  rw [← BlockRotationData.uniform_volume B blocks hu] at hbound
  exact (reverse_hoare source dest p q blocks B hu bs countBits hb hn).consequence
    (fun _ h => h) (fun _ h => h) hbound

end IntegerMultBounds.Machine.BlockReverseStream

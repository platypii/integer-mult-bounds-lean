import IntegerMultBounds.Machine.CountedRotateAdvance
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.CountedLoop
import IntegerMultBounds.Machine.GrowingCounterData

/-! A single fixed body for shifting successive equal-length raw fibers.
The offset and binary length descriptors are reused unchanged. All payload
contents remain implicit in their physical stream positions. -/

namespace IntegerMultBounds.Machine.FiberShift

open CountedRotate (bank)

variable {α : Type*}

def shift (cut : ℕ) (xs : List α) : List α := xs.drop cut ++ xs.take cut

@[simp] theorem shift_length (cut : ℕ) (xs : List α) : (shift cut xs).length = xs.length := by
  simp only [shift,List.length_append,List.length_drop,List.length_take]
  omega

def outputPrefix (cut i : ℕ) (fibers : List (List α)) : List α :=
  ((fibers.take i).map (shift cut)).flatten

theorem prefix_succ (cut i : ℕ) (fibers : List (List α)) (hi : i < fibers.length) :
    outputPrefix cut (i+1) fibers = outputPrefix cut i fibers ++ shift cut fibers[i] := by
  simp only [outputPrefix,List.take_succ_eq_append_getElem hi,List.map_append,List.flatten_append,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]

theorem prefix_length (cut i L : ℕ) (fibers : List (List α))
    (hu : BlockRotationData.Uniform L fibers) (hi : i ≤ fibers.length) :
    (outputPrefix cut i fibers).length = i*L := by
  have hh : BlockRotationData.Uniform L ((fibers.take i).map (shift cut)) := by
    intro xs hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    simpa only [shift_length] using hu ys (List.mem_of_mem_take hy)
  rw [outputPrefix,BlockRotationData.uniform_volume L _ hh,List.length_map,List.length_take,Nat.min_eq_left hi]

/-- The already placed source contains its i-th complete fiber at offset iL. -/
theorem source_fiber (f : ℤ → Fin 4) (p : ℤ) (fibers : List (List (Fin 4)))
    (L i : ℕ) (hu : BlockRotationData.Uniform L fibers) (hi : i < fibers.length) :
    putWord (putWord f p fibers.flatten) (p+((i*L : ℕ) : ℤ)) fibers[i] =
      putWord f p fibers.flatten := by
  have hleft : (fibers.take i).flatten.length = i*L := by
    rw [BlockRotationData.uniform_volume L _ (fun x hx => hu x (List.mem_of_mem_take hx)),
      List.length_take,Nat.min_eq_left hi.le]
  have hsplit : (fibers.take i).flatten ++ fibers[i] ++ (fibers.drop (i+1)).flatten = fibers.flatten := by
    rw [List.append_assoc,← List.flatten_cons,← List.drop_eq_getElem_cons hi,
      ← List.flatten_append,List.take_append_drop]
  have hh := WordSegments.middle f p (fibers.take i).flatten fibers[i] (fibers.drop (i+1)).flatten
  rw [hsplit,hleft] at hh
  exact hh

/-- The source is fixed; only the destination outputPrefix and the two payload heads
change between iterations. All three descriptors and the inner clock survive. -/
def state (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (b c d : List Bool) (i : ℕ) : Tapes 6 0 :=
  bank (putWord source p fibers.flatten) (putWord dest q (outputPrefix cut i fibers)) b c d
    (p+((i*L : ℕ) : ℤ)) (q+((i*L : ℕ) : ℤ))

def bodyBound (L : ℕ) (b c d : List Bool) : ℕ :=
  15*L+14*b.length+14*c.length+7*d.length+84

/-- The actual fixed body rotates the next fiber, preserving every prior output
and every source cell, with no scan of any earlier fiber. -/
theorem body_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (hu : BlockRotationData.Uniform L fibers) (hcut : cut ≤ L)
    (b c d : List Bool) (hb : Counter.value b = cut) (hc : Counter.value c = L-cut)
    (hd : Counter.value d = L) (i : ℕ) (hi : i < fibers.length) :
    HoareTime CountedRotateAdvance.program
      (fun v => v = state source dest p q fibers cut L b c d i)
      (fun v => v = state source dest p q fibers cut L b c d (i+1))
      (bodyBound L b c d) := by
  have hrow : fibers[i].length = L := hu _ (List.getElem_mem hi)
  have htake : (fibers[i].take cut).length = cut := by simp only [List.length_take,hrow,Nat.min_eq_left hcut]
  have hdrop : (fibers[i].drop cut).length = L-cut := by simp only [List.length_drop,hrow]
  have hsum : cut+(L-cut) = L := Nat.add_sub_of_le hcut
  have h := CountedRotateAdvance.rotate_hoare (putWord source p fibers.flatten)
    (putWord dest q (outputPrefix cut i fibers)) (p+((i*L : ℕ) : ℤ)) (q+((i*L : ℕ) : ℤ))
    (fibers[i].take cut) (fibers[i].drop cut) b c d
    (by simpa only [htake] using hb) (by simpa only [hdrop] using hc)
    (by simpa only [htake,hdrop,hsum] using hd)
  rw [List.take_append_drop,htake,hdrop,hsum,source_fiber source p fibers L i hu hi] at h
  change HoareTime CountedRotateAdvance.program
    (fun v => v = state source dest p q fibers cut L b c d i)
    (fun v => v = bank (putWord source p fibers.flatten)
      (putWord (putWord dest q (outputPrefix cut i fibers)) (q+((i*L : ℕ) : ℤ)) (shift cut fibers[i])) b c d
      (p+((i*L : ℕ) : ℤ)+L) (q+((i*L : ℕ) : ℤ)+L)) (bodyBound L b c d) at h
  have hout : putWord (putWord dest q (outputPrefix cut i fibers)) (q+((i*L : ℕ) : ℤ)) (shift cut fibers[i]) =
      putWord dest q (outputPrefix cut (i+1) fibers) := by
    rw [← prefix_length cut i L fibers hu hi.le,putWord_append_forward,prefix_succ cut i fibers hi]
  rw [hout] at h
  have hlen : (i+1)*L = i*L+L := by ring
  simpa only [state,hlen,Nat.cast_add,add_assoc] using h

/-- One fixed seven-tape machine, independent of fiber count and lengths. -/
def program : Program 7 85 0 := CountedLoop.program CountedRotateAdvance.program

/-- Complete repeated shifting of equal-length fibers by the same cut. The
separate outer clock controls exactly the number of fibers; every inner clock
is prepared and erased by the body and all data heads advance physically. -/
theorem shift_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (hu : BlockRotationData.Uniform L fibers) (hcut : cut ≤ L)
    (b c d countBits : List Bool) (hb : Counter.value b = cut) (hc : Counter.value c = L-cut)
    (hd : Counter.value d = L) (hn : Counter.value countBits = fibers.length) :
    HoareTime program
      (fun v => v = CountedLoop.bank
        (bank (putWord source p fibers.flatten) dest b c d p q) CountedCopyReuse.empty countBits)
      (fun v => v = CountedLoop.bank
        (bank (putWord source p fibers.flatten) (putWord dest q (fibers.map (shift cut)).flatten) b c d
          (p+((fibers.length*L : ℕ) : ℤ)) (q+((fibers.length*L : ℕ) : ℤ))) CountedCopyReuse.empty
        (List.replicate countBits.length true))
      (fibers.length*(bodyBound L b c d+6)+2*countBits.length+2) := by
  have h := CountedLoop.loop_hoare CountedRotateAdvance.program CountedCopyReuse.empty countBits
    fibers.length (state source dest p q fibers cut L b c d) (fun _ => bodyBound L b c d)
    hn (by simp [CountedCopyReuse.empty])
    (by simp [CountedCopyReuse.empty,show (1 : ℤ)+countBits.length ≠ 0 by omega])
    (body_hoare source dest p q fibers cut L hu hcut b c d hb hc hd)
  have hcost : (∑ _i ∈ Finset.range fibers.length, bodyBound L b c d)+6*fibers.length+
      2*countBits.length+2 = fibers.length*(bodyBound L b c d+6)+2*countBits.length+2 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at h
  simpa only [program,state,outputPrefix,List.take_zero,List.map_nil,List.flatten_nil,
    putWord,zero_mul,Nat.cast_zero,add_zero,List.take_length] using h

/-- Descriptor overhead is linear in total payload volume when descriptor
widths have their canonical elementary bounds and each fiber is nonempty.
No descriptor construction cost is hidden in this execution theorem. -/
theorem linear_bound (L n : ℕ) (b c d countBits : List Bool) (hL : 1 ≤ L)
    (hb : b.length ≤ L+1) (hc : c.length ≤ L+1) (hd : d.length ≤ L+1)
    (hn : countBits.length ≤ n+1) :
    n*(bodyBound L b c d+6)+2*countBits.length+2 ≤ 177*(n*L)+4 := by
  have hbody : bodyBound L b c d+6 ≤ 175*L := by
    dsimp only [bodyBound]
    omega
  have hh := Nat.mul_le_mul_left n hbody
  have hnl : n ≤ n*L := by nlinarith
  nlinarith

private theorem canonical_width_le (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs+1 := by
  have hw := GrowingCounterData.canonical_width bs h
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

/-- For canonical prepared descriptors, the complete repeated-fiber machine
has a genuine linear-volume runtime, with a uniform explicit constant. -/
theorem shift_hoare_linear (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (hu : BlockRotationData.Uniform L fibers) (hcut : cut ≤ L) (hL : 1 ≤ L)
    (b c d countBits : List Bool) (hb : Counter.value b = cut) (hc : Counter.value c = L-cut)
    (hd : Counter.value d = L) (hn : Counter.value countBits = fibers.length)
    (cb : GrowingCounterData.Canonical b) (cc : GrowingCounterData.Canonical c)
    (cd : GrowingCounterData.Canonical d) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime program
      (fun v => v = CountedLoop.bank
        (bank (putWord source p fibers.flatten) dest b c d p q) CountedCopyReuse.empty countBits)
      (fun v => v = CountedLoop.bank
        (bank (putWord source p fibers.flatten) (putWord dest q (fibers.map (shift cut)).flatten) b c d
          (p+((fibers.length*L : ℕ) : ℤ)) (q+((fibers.length*L : ℕ) : ℤ))) CountedCopyReuse.empty
        (List.replicate countBits.length true)) (177*fibers.flatten.length+4) := by
  have wb := canonical_width_le b cb
  have wc := canonical_width_le c cc
  have wd := canonical_width_le d cd
  have wn := canonical_width_le countBits cn
  rw [hb] at wb
  rw [hc] at wc
  rw [hd] at wd
  rw [hn] at wn
  have hbnd := linear_bound L fibers.length b c d countBits hL (by omega) (by omega) wd wn
  rw [← BlockRotationData.uniform_volume L fibers hu] at hbnd
  exact (shift_hoare source dest p q fibers cut L hu hcut b c d countBits hb hc hd hn).consequence
    (fun _ h => h) (fun _ h => h) hbnd

end IntegerMultBounds.Machine.FiberShift

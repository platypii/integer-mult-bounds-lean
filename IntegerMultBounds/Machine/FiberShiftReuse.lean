import IntegerMultBounds.Machine.FiberShift
import IntegerMultBounds.Machine.CountedLoopReuse

/-! Repeated common-offset fiber shifting with the entire outer count setup
and cleanup physically executed. Every mutable clock is restored and every
immutable descriptor survives. Derived descriptor arithmetic remains separate. -/

namespace IntegerMultBounds.Machine.FiberShiftReuse

open CountedRotate (bank)
open FiberShift (shift state bodyBound)

def program : Program 8 96 0 := CountedLoopReuse.program CountedRotateAdvance.program

/-- Actual repeated fiber shifts with both inner and outer work clocks restored
and all four immutable descriptors unchanged at their original head positions. -/
theorem shift_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (hu : BlockRotationData.Uniform L fibers) (hcut : cut ≤ L)
    (b c d countBits : List Bool) (hb : Counter.value b = cut) (hc : Counter.value c = L-cut)
    (hd : Counter.value d = L) (hn : Counter.value countBits = fibers.length) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p fibers.flatten) dest b c d p q)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p fibers.flatten) (putWord dest q (fibers.map (shift cut)).flatten) b c d
          (p+((fibers.length*L : ℕ) : ℤ)) (q+((fibers.length*L : ℕ) : ℤ)))
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fibers.length*(bodyBound L b c d+6)+7*countBits.length+16) := by
  have h := CountedLoopReuse.loop_hoare CountedRotateAdvance.program countBits fibers.length
    (state source dest p q fibers cut L b c d) (fun _ => bodyBound L b c d) hn
    (FiberShift.body_hoare source dest p q fibers cut L hu hcut b c d hb hc hd)
  have hcost : (∑ _i ∈ Finset.range fibers.length, bodyBound L b c d)+6*fibers.length+
      7*countBits.length+16 = fibers.length*(bodyBound L b c d+6)+7*countBits.length+16 := by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    ring
  rw [hcost] at h
  simpa only [program,state,FiberShift.outputPrefix,List.take_zero,List.map_nil,List.flatten_nil,
    putWord,zero_mul,Nat.cast_zero,add_zero,List.take_length] using h

private theorem width_le (bs : List Bool) (h : GrowingCounterData.Canonical bs) :
    bs.length ≤ Counter.value bs+1 := by
  have hw := GrowingCounterData.canonical_width bs h
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

theorem linear_bound (L n : ℕ) (b c d countBits : List Bool) (hL : 1 ≤ L)
    (hb : b.length ≤ L+1) (hc : c.length ≤ L+1) (hd : d.length ≤ L+1)
    (hn : countBits.length ≤ n+1) :
    n*(bodyBound L b c d+6)+7*countBits.length+16 ≤ 182*(n*L)+23 := by
  have hbody : bodyBound L b c d+6 ≤ 175*L := by dsimp only [bodyBound]; omega
  have hh := Nat.mul_le_mul_left n hbody
  have hnl : n ≤ n*L := by nlinarith
  nlinarith

/-- Linear in payload volume, including preparation and cleanup of the outer
mutable count. The canonical immutable descriptors remain explicit inputs. -/
theorem shift_hoare_linear (source dest : ℤ → Fin 4) (p q : ℤ) (fibers : List (List (Fin 4)))
    (cut L : ℕ) (hu : BlockRotationData.Uniform L fibers) (hcut : cut ≤ L) (hL : 1 ≤ L)
    (b c d countBits : List Bool) (hb : Counter.value b = cut) (hc : Counter.value c = L-cut)
    (hd : Counter.value d = L) (hn : Counter.value countBits = fibers.length)
    (cb : GrowingCounterData.Canonical b) (cc : GrowingCounterData.Canonical c)
    (cd : GrowingCounterData.Canonical d) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime program
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p fibers.flatten) dest b c d p q)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (putWord source p fibers.flatten) (putWord dest q (fibers.map (shift cut)).flatten) b c d
          (p+((fibers.length*L : ℕ) : ℤ)) (q+((fibers.length*L : ℕ) : ℤ)))
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (182*fibers.flatten.length+23) := by
  have wb := width_le b cb
  have wc := width_le c cc
  have wd := width_le d cd
  have wn := width_le countBits cn
  rw [hb] at wb
  rw [hc] at wc
  rw [hd] at wd
  rw [hn] at wn
  have hbound := linear_bound L fibers.length b c d countBits hL (by omega) (by omega) wd wn
  rw [← BlockRotationData.uniform_volume L fibers hu] at hbound
  exact (shift_hoare source dest p q fibers cut L hu hcut b c d countBits hb hc hd hn).consequence
    (fun _ h => h) (fun _ h => h) hbound

end IntegerMultBounds.Machine.FiberShiftReuse

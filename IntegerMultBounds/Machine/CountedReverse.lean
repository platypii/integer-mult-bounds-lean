import IntegerMultBounds.Machine.CountedCopy
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Reflection

/-! Counted backwards reading with forwards output. The binary clock keeps its
normal orientation. All payload symbols, including blanks, are reversed by real
head movements; the source and all other destination cells are preserved. -/

namespace IntegerMultBounds.Machine.CountedReverse

open CountedCopy

/-- Reverse only source-tape motion; the counter still ripples to the right. -/
def mask (i : Fin 3) : Bool := decide (i = 0)

def program : Program 3 5 0 := Reflection.program CountedCopy.program mask

private theorem reflected_cfg (f g clock : ℤ → Fin 4) (p q r : ℤ) (s : Fin 5) :
    Reflection.config mask (cfg f g clock p q r s) =
      cfg (fun j => f (-j)) g clock (-p) q r s := by
  simp only [Reflection.config,Reflection.tapes,Config.tapes,cfg]
  congr 1
  · funext i
    fin_cases i <;> simp [mask,Reflection.coord]
  · funext i j
    fin_cases i <;> simp [mask,Reflection.coord]

/-- Exact reversed output, with every counter scan and return included.
Initial positioning at the source's last cell and preparing the count are
explicit preconditions; the final source head is one cell before the block. -/
theorem reverse_exact (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    runtime xs.length bs ≤ 5*xs.length+2*bs.length+2 ∧
    run program (runtime xs.length bs)
      (cfg (putWord source p xs) dest (putBits clock 1 bs) (p+xs.length-1) q 1 0) =
      some (cfg (putWord source p xs) (putWord dest q xs.reverse)
        (putBits clock 1 (List.replicate bs.length true)) (p-1) (q+xs.length) 1 4) ∧
    step program (cfg (putWord source p xs) (putWord dest q xs.reverse)
      (putBits clock 1 (List.replicate bs.length true)) (p-1) (q+xs.length) 1 4) = none := by
  obtain ⟨hb,hr,hh⟩ := copy_exact (fun j => source (-j)) dest clock
    (-p-xs.length+1) q xs.reverse bs (by simpa using hcount) hzero hend
  have hw : (fun j => putWord (fun k => source (-k)) (-p-xs.length+1) xs.reverse (-j)) =
      putWord source p xs := by
    rw [Reflection.word,List.reverse_reverse,List.length_reverse]
    have hpos : -(-p-(xs.length : ℤ)+1)-xs.length+1 = p := by omega
    rw [hpos]
    simp
  have hp : -(-p-(xs.length : ℤ)+1) = p+xs.length-1 := by omega
  have hp' : -(-p-(xs.length : ℤ)+1+xs.length) = p-1 := by omega
  have hrun := Reflection.run_eq CountedCopy.program mask (runtime xs.reverse.length bs)
    (cfg (putWord (fun j => source (-j)) (-p-xs.length+1) xs.reverse)
      dest (putBits clock 1 bs) (-p-xs.length+1) q 1 0)
  rw [hr] at hrun
  have hhalt := Reflection.step_eq CountedCopy.program mask
    (cfg (putWord (fun j => source (-j)) (-p-xs.length+1) xs.reverse)
      (putWord dest q xs.reverse) (putBits clock 1 (List.replicate bs.length true))
      (-p-xs.length+1+xs.reverse.length) (q+xs.reverse.length) 1 4)
  rw [hh] at hhalt
  refine ⟨by simpa using hb,?_,?_⟩
  · simpa only [program,Option.map_some,reflected_cfg,List.length_reverse,hw,hp,hp'] using hrun
  · simpa only [program,Option.map_none,reflected_cfg,List.length_reverse,hw,hp'] using hhalt

/-- Hoare form for a raw reversed copy, with arbitrary tape backgrounds. -/
theorem reverse_hoare (source dest clock : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hzero : clock 0 = separator) (hend : clock (1+bs.length) = blank) :
    HoareTime program
      (fun v => v = (cfg (putWord source p xs) dest (putBits clock 1 bs)
        (p+xs.length-1) q 1 0).tapes)
      (fun v => v = (cfg (putWord source p xs) (putWord dest q xs.reverse)
        (putBits clock 1 (List.replicate bs.length true)) (p-1) (q+xs.length) 1 4).tapes)
      (5*xs.length+2*bs.length+2) := by
  rintro v rfl
  obtain ⟨hb,hr,hh⟩ := reverse_exact source dest clock p q xs bs hcount hzero hend
  exact ⟨runtime xs.length bs,_,hb,hr,hh,rfl⟩

namespace Reusable

open CountedCopyReuse (bank empty binary)

def mask (i : Fin 4) : Bool := decide (i = 0)

def program : Program 4 16 0 := Reflection.program CountedCopyReuse.program mask

private theorem reflected_bank (f g clock descriptor : ℤ → Fin 4) (p q r s : ℤ) :
    Reflection.tapes mask (bank f g clock descriptor p q r s) =
      bank (fun j => f (-j)) g clock descriptor (-p) q r s := by
  simp only [Reflection.tapes,bank]
  congr 1
  · funext i
    fin_cases i <;> simp [mask,Reflection.coord]
  · funext i j
    fin_cases i <;> simp [mask,Reflection.coord]

/-- Reversed copying with the descriptor preserved and the work clock restored.
The bound includes physical clock preparation, erasure, resets, and all joins. -/
theorem reverse_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length) :
    HoareTime program
      (fun v => v = bank (putWord source p xs) dest empty (binary bs) (p+xs.length-1) q 1 1)
      (fun v => v = bank (putWord source p xs) (putWord dest q xs.reverse) empty (binary bs)
        (p-1) (q+xs.length) 1 1)
      (5*xs.length+7*bs.length+16) := by
  have h := Reflection.hoare (CountedCopyReuse.copy_hoare (fun j => source (-j)) dest
    (-p-xs.length+1) q xs.reverse bs (by simpa using hcount)) mask
  have hw : (fun j => putWord (fun k => source (-k)) (-p-xs.length+1) xs.reverse (-j)) =
      putWord source p xs := by
    rw [Reflection.word,List.reverse_reverse,List.length_reverse]
    have hpos : -(-p-(xs.length : ℤ)+1)-xs.length+1 = p := by omega
    rw [hpos]
    simp
  have hp : -(-p-(xs.length : ℤ)+1) = p+xs.length-1 := by omega
  have hp' : -(-p-(xs.length : ℤ)+1+xs.length) = p-1 := by omega
  apply h.consequence
  · rintro v rfl
    refine ⟨_,rfl,?_⟩
    rw [reflected_bank,hw,hp]
  · rintro v ⟨original,rfl,rfl⟩
    rw [reflected_bank,hw,List.length_reverse,hp']
  · simp

end Reusable

end IntegerMultBounds.Machine.CountedReverse

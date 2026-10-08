import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.GrowingCounterData

/-! Reusable arbitrary-alphabet head positioning. The literal body preserves
every scanned symbol and moves one cell in a fixed direction. A binary-counted
loop charges every movement, countdown, descriptor copy, reset and join. -/
namespace IntegerMultBounds.Machine.CountedPosition
variable {a : ℕ}

def cell (m : Move) : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then some (1,fun i => (sy i,m)) else none

def one (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩

theorem cell_hoare (m : Move) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (cell m) (fun v => v = one f p)
      (fun v => v = one f (p+m.offset)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+m.offset,fun _ => f⟩,le_rfl,?_,by simp [step,cell],rfl⟩
  rw [run_one]
  simp only [step,cell,one,Tapes.start,↓reduceIte]
  congr 1
  congr 1
  funext i j
  split_ifs with hj
  · subst j; simp
  · simp [hj]

def bank (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool) : Tapes 3 a :=
  CountedLoopReuseAlphabet.bank (one f p) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1

def program (m : Move) : Program 3 (7+(2+5)+4) a :=
  CountedLoopReuseAlphabet.program (cell m)

/-- Runtime distance is read from the preserved descriptor, never compiled
into machine states. Every payload symbol and the work clock are preserved. -/
theorem position_hoare (m : Move) (f : ℤ → Fin (a+4)) (p : ℤ) (bs : List Bool)
    (n : ℕ) (hc : Counter.value bs = n) :
    HoareTime (program m) (fun v => v = bank f p bs)
      (fun v => v = bank f (p+n*m.offset) bs) (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (cell m) bs n
    (fun i => one f (p+(i : ℤ)*m.offset)) (fun _ => 1) hc (by
      intro i _
      have he : p+(i : ℤ)*m.offset+m.offset = p+((i+1 : ℕ) : ℤ)*m.offset := by
        push_cast; ring
      simpa only [he] using cell_hoare m f (p+(i : ℤ)*m.offset))
  apply hh.consequence ?_ (fun _ h => h) ?_
  · intro v hv
    simpa only [bank,Nat.cast_zero,zero_mul,add_zero] using hv
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    omega

/-- Canonical descriptors give a uniform linear bound, also for distance zero. -/
theorem cost_linear (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    7*Counter.value bs+7*bs.length+16 ≤ 14*Counter.value bs+23 := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

end IntegerMultBounds.Machine.CountedPosition

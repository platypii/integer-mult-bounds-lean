import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! Delimiter-free erasure of an arbitrary raw segment, with an immutable length
and fully reusable clock. Every overwritten symbol and head move is charged. -/
namespace IntegerMultBounds.Machine.CountedErase

/-- Erase precisely the half-open interval, preserving the surrounding tape. -/
def erased (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) : ℤ → Fin 4 :=
  fun z => if p ≤ z ∧ z < p+n then blank else f z

@[simp] theorem erased_zero (f : ℤ → Fin 4) (p : ℤ) : erased f p 0 = f := by
  funext z
  simp [erased]

theorem erased_succ (f : ℤ → Fin 4) (p : ℤ) (n : ℕ) :
    Function.update (erased f p n) (p+n) blank = erased f p (n+1) := by
  funext z
  by_cases hz : z = p+n
  · subst z; simp [erased]
  · rw [Function.update_of_ne hz]
    simp only [erased]
    have he : (p ≤ z ∧ z < p+(n : ℤ)) ↔ (p ≤ z ∧ z < p+((n+1 : ℕ) : ℤ)) := by omega
    simp only [he]

def one (f : ℤ → Fin 4) (p : ℤ) : Tapes 1 0 := ⟨fun _ => p,fun _ => f⟩

/-- One actual write-and-advance transition, then a true halt. -/
def eraseCell : Program 1 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state _ => if state = 0 then some (1,fun _ => (blank,Move.right)) else none

theorem cell_hoare (f : ℤ → Fin 4) (p : ℤ) :
    HoareTime eraseCell (fun v => v = one f p)
      (fun v => v = one (Function.update f p blank) (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => p+1,fun _ => Function.update f p blank⟩,le_rfl,?_,?_,rfl⟩
  · simp [run_one,step,eraseCell,Tapes.start,one,Move.offset]
    funext i z
    by_cases h : z = p <;> simp [h]
  · simp [step,eraseCell]

def program : Program 3 18 0 := CountedLoopReuse.program eraseCell

def bank (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) : Tapes 3 0 :=
  CountedLoopReuse.bank (one f p) CountedCopyReuse.empty (CountedCopyReuse.binary bs) 1 1

/-- Raw erasure includes clock preparation and cleanup, even at length zero. -/
theorem erase_hoare (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    HoareTime program (fun v => v = bank f p bs)
      (fun v => v = bank (erased f p (Counter.value bs)) (p+Counter.value bs) bs)
      (7*Counter.value bs+7*bs.length+16) := by
  let v := fun i : ℕ => one (erased f p i) (p+i)
  have hb : ∀ i < Counter.value bs,
      HoareTime eraseCell (fun w => w = v i) (fun w => w = v (i+1)) 1 := by
    intro i _
    have h := cell_hoare (erased f p i) (p+i)
    rw [erased_succ] at h
    simpa only [v,Nat.cast_add,Nat.cast_one,add_assoc] using h
  have h := CountedLoopReuse.loop_hoare eraseCell bs (Counter.value bs) v (fun _ => 1) rfl hb
  simpa [program,bank,v,Nat.mul_succ,show ∀ n : ℕ, n+6*n = 7*n by omega] using h

/-- Erasing a scratch word restores its background when that interval was blank.
No assumption is made about other cells, which remain untouched. -/
theorem erased_word (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    erased (putWord f p xs) p xs.length = f := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+xs.length
  · simp only [erased,ite_eq_left hi]
    exact (hblank z hi.1 hi.2).symm
  · simp only [erased,ite_eq_right hi]
    exact putWord_outside f p z xs (by omega)

theorem erase_word_hoare (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    HoareTime program (fun v => v = bank (putWord f p xs) p bs)
      (fun v => v = bank f (p+xs.length) bs) (7*xs.length+7*bs.length+16) := by
  have h := erase_hoare (putWord f p xs) p bs
  simpa only [hcount,erased_word f p xs hblank] using h

/-- Canonical descriptors yield a linear-volume cleanup bound. -/
theorem erase_hoare_linear (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime program (fun v => v = bank f p bs)
      (fun v => v = bank (erased f p (Counter.value bs)) (p+Counter.value bs) bs)
      (14*Counter.value bs+23) := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self (Counter.value bs)
  exact (erase_hoare f p bs).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.CountedErase

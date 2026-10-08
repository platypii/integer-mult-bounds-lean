import IntegerMultBounds.Machine.CountedVolumeLoop
import IntegerMultBounds.Machine.WordSegments

/-! Physical normalization between affine array operations. Starting with both
payload heads at the end, rewind both, transfer every output cell to the common
input while clearing the output, then rewind both again. Canonical dimensions
B/Q/P are reused by actual nested loops; no product descriptor is supplied. -/
namespace IntegerMultBounds.Machine.FlatArrayNormalize
variable {a : ℕ}

def pair (source dest : ℤ → Fin (a+4)) (p q : ℤ) : Tapes 2 a := ⟨![p,q],![source,dest]⟩

def erased (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) : ℤ → Fin (a+4) :=
  fun z => if p ≤ z ∧ z < p+n then blank else f z

@[simp] theorem erased_zero (f : ℤ → Fin (a+4)) (p : ℤ) : erased f p 0 = f := by
  funext z; simp [erased]

theorem erased_succ (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) :
    Function.update (erased f p n) (p+n) blank = erased f p (n+1) := by
  funext z
  by_cases hz : z = p+n
  · subst z; simp [erased]
  · rw [Function.update_of_ne hz]
    simp only [erased]
    have he : (p ≤ z ∧ z < p+(n : ℤ)) ↔ (p ≤ z ∧ z < p+((n+1 : ℕ) : ℤ)) := by omega
    simp only [he]

theorem erased_word (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (hblank : ∀ z, p ≤ z → z < p+xs.length → f z = blank) :
    erased (putWord f p xs) p xs.length = f := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+xs.length
  · simp only [erased,ite_eq_left hi]
    exact (hblank z hi.1 hi.2).symm
  · simp only [erased,ite_eq_right hi]
    exact putWord_outside f p z xs (by omega)

/-- One transition moves both heads left, preserving their symbols. -/
def backCell : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then some (1,fun i => (symbols i,Move.left)) else none

/-- One transition copies the source symbol to the destination, erases the
source, and moves both heads right. Arbitrary payload symbols are permitted. -/
def moveCell : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (if i = 0 then blank else symbols 0,Move.right)) else none

theorem back_cell_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime backCell (fun v => v = pair f g p q)
      (fun v => v = pair f g (p-1) (q-1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,![p-1,q-1],![f,g]⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,backCell,Tapes.start,pair,↓reduceIte,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp <;> omega
    · funext i z; fin_cases i <;> simp <;> intro h <;> subst z <;> rfl
  · simp [step,backCell]

theorem move_cell_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    HoareTime moveCell (fun v => v = pair f g p q)
      (fun v => v = pair (Function.update f p blank) (Function.update g q (f p)) (p+1) (q+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,![p+1,q+1],![Function.update f p blank,Function.update g q (f p)]⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,moveCell,Tapes.start,pair,↓reduceIte,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp
    · funext i z; fin_cases i <;> simp [Function.update_apply]
  · simp [step,moveCell]

def bank (f g : ℤ → Fin (a+4)) (p q : ℤ) (bs qs ps : List Bool) : Tapes 8 a :=
  CountedVolumeLoop.bank (pair f g p q) bs qs ps

def rewindProgram : Program 8 50 a := CountedVolumeLoop.program backCell
def moveProgram : Program 8 50 a := CountedVolumeLoop.program moveCell

theorem rewind_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (P Q B : ℕ) (bs qs ps : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hp : Counter.value ps = P) :
    HoareTime rewindProgram (fun v => v = bank f g (p+((P*(Q*B) : ℕ) : ℤ)) (q+((P*(Q*B) : ℕ) : ℤ)) bs qs ps)
      (fun v => v = bank f g p q bs qs ps) (CountedVolumeLoop.bound 1 P Q B bs qs ps) := by
  have hh := CountedVolumeLoop.loop_hoare backCell P Q B 1 bs qs ps hb hq hp
    (fun i => pair f g (p+((P*(Q*B) : ℕ) : ℤ)-i) (q+((P*(Q*B) : ℕ) : ℤ)-i))
    (by intro i hi
        have h := back_cell_hoare f g (p+((P*(Q*B) : ℕ) : ℤ)-i) (q+((P*(Q*B) : ℕ) : ℤ)-i)
        have he (z : ℤ) : z-i-1 = z-((i+1 : ℕ) : ℤ) := by omega
        simpa only [he] using h)
  simpa only [rewindProgram,bank,Nat.cast_zero,sub_zero,add_sub_cancel_right] using hh

private theorem write_take (g : ℤ → Fin (a+4)) (q : ℤ) (xs : List (Fin (a+4))) (i : ℕ) (hi : i < xs.length) :
    Function.update (putWord g q (xs.take i)) (q+i) xs[i] = putWord g q (xs.take (i+1)) := by
  have hl : (xs.take i).length = i := List.length_take_of_le (by omega)
  have hh := putWord_append_forward g q (xs.take i) [xs[i]]
  simpa only [putWord,hl,List.take_succ_eq_append_getElem hi] using hh

theorem move_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ) (xs : List (Fin (a+4)))
    (P Q B : ℕ) (bs qs ps : List Bool) (hlen : xs.length = P*(Q*B))
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hp : Counter.value ps = P) :
    HoareTime moveProgram (fun v => v = bank (putWord f p xs) g p q bs qs ps)
      (fun v => v = bank (erased (putWord f p xs) p xs.length) (putWord g q xs)
        (p+xs.length) (q+xs.length) bs qs ps) (CountedVolumeLoop.bound 1 P Q B bs qs ps) := by
  let v := fun i => pair (erased (putWord f p xs) p i) (putWord g q (xs.take i)) (p+i) (q+i)
  have hh := CountedVolumeLoop.loop_hoare moveCell P Q B 1 bs qs ps hb hq hp v
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
def program : Program 8 150 a := seq (seq rewindProgram moveProgram) rewindProgram

/-- After normalization, the old output is blank again and the common input
contains the new flat word, with both heads at their actual origins. -/
theorem normalize_hoare (scratch common : ℤ → Fin (a+4)) (p q : ℤ) (xs : List (Fin (a+4)))
    (P Q B : ℕ) (bs qs ps : List Bool) (hlen : xs.length = P*(Q*B))
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (hp : Counter.value ps = P)
    (hP : 0 < P) (hQ : 0 < Q) (hB : 0 < B)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps)
    (hblank : ∀ z, p ≤ z → z < p+xs.length → scratch z = blank) :
    HoareTime program
      (fun v => v = bank (putWord scratch p xs) common (p+xs.length) (q+xs.length) bs qs ps)
      (fun v => v = bank scratch (putWord common q xs) p q bs qs ps)
      (327*xs.length+2) := by
  have h₀ := rewind_hoare (putWord scratch p xs) common p q P Q B bs qs ps hb hq hp
  have h₁ := move_hoare scratch common p q xs P Q B bs qs ps hlen hb hq hp
  rw [erased_word scratch p xs hblank] at h₁
  have h₂ := rewind_hoare scratch (putWord common q xs) p q P Q B bs qs ps hb hq hp
  rw [← hlen] at h₀ h₂
  apply ((h₀.seq h₁).seq h₂).consequence (fun _ h => h) (fun _ h => h) _
  have hbound := CountedVolumeLoop.bound_linear P Q B bs qs ps hP hQ hB hb hq hp cb cq cp
  rw [← hlen] at hbound
  omega

end IntegerMultBounds.Machine.FlatArrayNormalize

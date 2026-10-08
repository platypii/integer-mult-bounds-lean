import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.GrowingCounterData

/-! Delimiter-free simultaneous erasure and head restoration for any fixed
selection of payload tapes over the full native alphabet. Runtime lengths live
on an immutable descriptor, and every erased cell and return move is charged. -/
namespace IntegerMultBounds.Machine.CountedBankReset
variable {t a : ℕ}

def erased (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) : ℤ → Fin (a+4) :=
  fun z => if p ≤ z ∧ z < p+n then blank else f z

@[simp] theorem erased_zero (f : ℤ → Fin (a+4)) (p : ℤ) : erased f p 0 = f := by
  funext z
  simp [erased]

theorem erased_succ (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ) :
    Function.update (erased f p n) (p+n) blank = erased f p (n+1) := by
  funext z
  by_cases hz : z = p+n
  · subst z; simp [erased]
  · rw [Function.update_of_ne hz]
    simp only [erased]
    have he : (p ≤ z ∧ z < p+(n : ℤ)) ↔ (p ≤ z ∧ z < p+((n+1 : ℕ) : ℤ)) := by omega
    simp only [he]

theorem erased_word (xs : List (Fin (a+4))) (p : ℤ) :
    erased (putWord (fun _ => blank) p xs) p xs.length = fun _ => blank := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+xs.length
  · simp [erased,hi]
  · simp only [erased,ite_eq_right hi]
    exact putWord_outside _ p z xs (by omega)

def after (selected : Fin t → Bool) (v : Tapes t a) (n : ℕ) : Tapes t a where
  head i := if selected i then v.head i+n else v.head i
  tape i := if selected i then erased (v.tape i) (v.head i) n else v.tape i

def restored (selected : Fin t → Bool) (v : Tapes t a) (n : ℕ) : Tapes t a :=
  ⟨v.head,(after selected v n).tape⟩

def eraseCell (ht : 0 < t) (selected : Fin t → Bool) : Program t 2 a where
  tapes_pos := ht
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i =>
    (if selected i then blank else sy i,if selected i then .right else .stay)) else none

theorem eraseCell_hoare (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (n : ℕ) :
    HoareTime (eraseCell ht selected) (fun w => w = after selected v n)
      (fun w => w = after selected v (n+1)) 1 := by
  rintro w rfl
  refine ⟨1,⟨1,(after selected v (n+1)).head,(after selected v (n+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,eraseCell,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases hi : selected i <;> simp [after,hi,Move.offset] <;> omega
    · funext i z
      cases hi : selected i
      · simp [after,hi]
        intro hz; subst z; rfl
      · simpa only [after,hi,ite_true,Function.update_apply] using congrFun (erased_succ (v.tape i) (v.head i) n) z
  · simp [step,eraseCell]

def bank (v : Tapes t a) (bs : List Bool) :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def eraseProgram (ht : 0 < t) (selected : Fin t → Bool) :=
  CountedLoopReuseAlphabet.program (eraseCell (a := a) ht selected)

theorem erase_hoare (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) :
    HoareTime (eraseProgram ht selected) (fun w => w = bank v bs)
      (fun w => w = bank (after selected v n) bs) (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (eraseCell ht selected) bs n
    (after selected v) (fun _ => 1) hn (fun i _ => eraseCell_hoare ht selected v i)
  have hz : after selected v 0 = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [after]
  simpa only [eraseProgram,bank,hz,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show n+6*n = 7*n by omega] using hh

def rewindCell (ht : 0 < t) (selected : Fin t → Bool) : Program t 2 a where
  tapes_pos := ht
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i =>
    (sy i,if selected i then .left else .stay)) else none

def rewound (selected : Fin t → Bool) (v : Tapes t a) (k : ℕ) : Tapes t a :=
  ⟨fun i => if selected i then v.head i-k else v.head i,v.tape⟩

theorem rewindCell_hoare (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (k : ℕ) :
    HoareTime (rewindCell ht selected) (fun w => w = rewound selected v k)
      (fun w => w = rewound selected v (k+1)) 1 := by
  rintro w rfl
  refine ⟨1,⟨1,(rewound selected v (k+1)).head,v.tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,rewindCell,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases hi : selected i <;> simp [rewound,hi,Move.offset] <;> omega
    · funext i z
      cases hi : selected i <;> simp [rewound,hi] <;>
        (intro hz; subst z; rfl)
  · simp [step,rewindCell]

def rewindProgram (ht : 0 < t) (selected : Fin t → Bool) :=
  CountedLoopReuseAlphabet.program (rewindCell (a := a) ht selected)

theorem rewind_hoare (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) :
    HoareTime (rewindProgram ht selected) (fun w => w = bank v bs)
      (fun w => w = bank (rewound selected v n) bs) (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare (rewindCell ht selected) bs n
    (rewound selected v) (fun _ => 1) hn (fun i _ => rewindCell_hoare ht selected v i)
  have hz : rewound selected v 0 = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [rewound]
  simpa only [rewindProgram,bank,hz,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show n+6*n = 7*n by omega] using hh

def program (ht : 0 < t) (selected : Fin t → Bool) :=
  seq (eraseProgram (a := a) ht selected) (rewindProgram ht selected)

theorem resets_hoare (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) :
    HoareTime (program ht selected) (fun w => w = bank v bs)
      (fun w => w = bank (restored selected v n) bs) (14*n+14*bs.length+33) := by
  have hh := (erase_hoare ht selected v bs n hn).seq (rewind_hoare ht selected (after selected v n) bs n hn)
  have he : rewound selected (after selected v n) n = restored selected v n := by
    apply congrArg₂ Tapes.mk
    · funext i; cases hi : selected i <;> simp [rewound,after,restored,hi]
    · rfl
  exact hh.consequence (fun _ h => h) (fun _ h => by simpa only [he] using h) (by omega)

theorem resets_hoare_linear (ht : 0 < t) (selected : Fin t → Bool) (v : Tapes t a) (bs : List Bool) (n : ℕ)
    (hn : Counter.value bs = n) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program ht selected) (fun w => w = bank v bs)
      (fun w => w = bank (restored selected v n) bs) (28*n+47) := by
  have hw := GrowingCounterData.canonical_width bs hc
  rw [hn] at hw
  have hl := Nat.log2_le_self n
  exact (resets_hoare ht selected v bs n hn).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.CountedBankReset

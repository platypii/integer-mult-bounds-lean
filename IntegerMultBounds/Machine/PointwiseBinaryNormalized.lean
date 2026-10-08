import IntegerMultBounds.Machine.PointwiseBinary
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.GrowingCounterData

/-! A pointwise finite-symbol operation followed by an actual counted rewind
of both payload heads. The same length descriptor and work clock are reused;
all original heads and every out-of-word cell are preserved exactly. -/
namespace IntegerMultBounds.Machine.PointwiseBinaryNormalized
variable {a : ℕ}

def shifted (v : Tapes 2 a) (d : ℤ) : Tapes 2 a := ⟨fun i => v.head i+d,v.tape⟩

def backCell : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then some (1,fun i => (sy i,.left)) else none

theorem back_cell_hoare (v : Tapes 2 a) :
    HoareTime backCell (fun w => w = v) (fun w => w = shifted v (-1)) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(shifted v (-1)).head,v.tape⟩,le_rfl,?_,by simp [step,backCell],rfl⟩
  simp only [run_one,step,backCell,Tapes.start,↓reduceIte,shifted,Move.offset]
  congr 1
  congr 1
  funext i j
  by_cases hj : j = v.head i
  · subst j; simp
  · simp [hj]

def bank (v : Tapes 2 a) (bs : List Bool) :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def rewindProgram : Program 4 18 a := CountedLoopReuseAlphabet.program backCell

theorem rewind_hoare (v : Tapes 2 a) (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime rewindProgram (fun w => w = bank (shifted v n) bs)
      (fun w => w = bank v bs) (7*n+7*bs.length+16) := by
  have hh := CountedLoopReuseAlphabet.loop_hoare backCell bs n
    (fun i => shifted v ((n : ℤ)-i)) (fun _ => 1) hn
    (by intro i _
        have h := back_cell_hoare (shifted v ((n : ℤ)-i))
        have he : shifted (shifted v ((n : ℤ)-i)) (-1) = shifted v ((n : ℤ)-(i+1 : ℕ)) := by
          apply congrArg₂ Tapes.mk
          · funext j; simp only [shifted,Nat.cast_add,Nat.cast_one]; omega
          · rfl
        rw [he] at h
        exact h)
  have hz : shifted v 0 = v := by cases v; simp [shifted]
  simpa only [rewindProgram,bank,Nat.cast_zero,sub_zero,sub_self,hz,
    Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show n+6*n = 7*n by omega] using hh

def output (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a) (n : ℕ) : Tapes 2 a :=
  ⟨v.head,(PointwiseBinary.result op v n).tape⟩

def program (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) :=
  seq (PointwiseBinary.program op) rewindProgram

theorem apply_hoare (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (v : Tapes 2 a)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (program op) (fun w => w = bank v bs)
      (fun w => w = bank (output op v n) bs) (14*n+14*bs.length+33) := by
  have hs := PointwiseBinary.apply_hoare op v bs n hn
  have hr := rewind_hoare (output op v n) bs n hn
  have he : shifted (output op v n) n = PointwiseBinary.result op v n := by
    apply congrArg₂ Tapes.mk
    · funext i; exact (PointwiseBinary.heads op v n i).symm
    · rfl
  rw [he] at hr
  exact (hs.seq hr).consequence (fun _ h => h) (fun _ h => h) (by omega)

def pair (source dest : ℤ → Fin (a+4)) (p q : ℤ) (x y : Fin n → Fin (a+4)) : Tapes 2 a :=
  StackPop.bank (putWord source p (List.ofFn x)) (putWord dest q (List.ofFn y)) p q

theorem output_array (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
    (source dest : ℤ → Fin (a+4)) (p q : ℤ) (x y : Fin n → Fin (a+4)) :
    output op (pair source dest p q x y) n = pair source dest p q x (fun i => op (x i) (y i)) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i z
    fin_cases i
    · exact congrFun (PointwiseBinary.source op (pair source dest p q x y) n) z
    · change (PointwiseBinary.result op (pair source dest p q x y) n).tape 1 z =
        putWord dest q (List.ofFn (fun i => op (x i) (y i))) z
      rw [PointwiseBinary.destination]
      simp only [pair,StackPop.bank,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true]
      by_cases hz : q ≤ z ∧ z < q+n
      · rw [ite_eq_left hz]
        let k : Fin n := ⟨(z-q).toNat,by omega⟩
        have he : (k.val : ℤ) = z-q := Int.toNat_of_nonneg (by omega)
        have hz' : z = q+k.val := by omega
        have hs := WordSegments.get source p (List.ofFn x) k.val (by simp)
        have hd := WordSegments.get dest q (List.ofFn y) k.val (by simp)
        have ho := WordSegments.get dest q (List.ofFn (fun i => op (x i) (y i))) k.val (by simp)
        simp only [List.getElem_ofFn] at hs hd ho
        rw [← he,hs,hz',hd,ho]
      · rw [ite_eq_right hz]
        rw [putWord_outside dest q z (List.ofFn y) (by simp only [List.length_ofFn]; omega),
          putWord_outside dest q z (List.ofFn (fun i => op (x i) (y i))) (by simp only [List.length_ofFn]; omega)]

theorem array_hoare (op : Fin (a+4) → Fin (a+4) → Fin (a+4))
    (source dest : ℤ → Fin (a+4)) (p q : ℤ) (x y : Fin n → Fin (a+4))
    (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program op) (fun w => w = bank (pair source dest p q x y) bs)
      (fun w => w = bank (pair source dest p q x (fun i => op (x i) (y i))) bs)
      (14*n+14*bs.length+33) := by
  simpa only [output_array] using apply_hoare op (pair source dest p q x y) bs n hn

/-- Encoded-bit XOR with exact arrays, arbitrary tape backgrounds, original
payload heads, and restored controls. -/
theorem xor_hoare (source dest : ℤ → Fin (a+4)) (p q : ℤ) (x y : Fin n → Bool)
    (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program PointwiseBinary.xorSymbol)
      (fun w => w = bank (pair source dest p q (fun i => bitSymbol (x i)) (fun i => bitSymbol (y i))) bs)
      (fun w => w = bank (pair source dest p q (fun i => bitSymbol (x i))
        (fun i => bitSymbol (Bool.xor (x i) (y i)))) bs)
      (14*n+14*bs.length+33) := by
  simpa only [PointwiseBinary.xorSymbol_bits] using array_hoare PointwiseBinary.xorSymbol source dest p q
    (fun i => bitSymbol (x i)) (fun i => bitSymbol (y i)) bs hn

theorem cost_linear (bs : List Bool) (hn : GrowingCounterData.Canonical bs) :
    14*Counter.value bs+14*bs.length+33 ≤ 28*Counter.value bs+47 := by
  have hw := GrowingCounterData.canonical_width bs hn
  have hl := Nat.log2_le_self (Counter.value bs)
  omega

end IntegerMultBounds.Machine.PointwiseBinaryNormalized

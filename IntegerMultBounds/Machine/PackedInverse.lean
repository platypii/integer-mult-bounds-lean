import IntegerMultBounds.Machine.PackedArith

/-! The inverse packed program of the compact-control address arithmetic on
nine tapes: the four packed updates of `packedEarly` undone in reverse order
with negated offsets, each a gather-and-transduce line. From the output words
of the forward program it recovers the input words; the input words and the
control are preserved, the offset scratch is blank again, and the recovered
words sit on their own tapes with every head at its origin. -/

namespace IntegerMultBounds.Machine.PackedInverse

variable {a : ℕ}

open ColumnTransducer (Rule addRule subRule digits)
open Gather (Shape gather)
open PackedArith (maskShift parity controlsAt)

/-- The nine-tape bank: `V₂`, `W₂`, `Z`, `W₁`, `T`, `V₁`, `W`, offset scratch, `V`. -/
def bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) : Tapes 9 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7 else p8,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3
    else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7 else f8⟩

section Lists

/-- Undo the fourth line: add back the toggled parities of `V₂`. -/
def off1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 Z : List Bool) : List Bool :=
  gather (fun x z => xor x z) (parity q b hb hbq) V2 Z Z.length
def w1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  digits addRule 0 (W2.zip (off1 q b hb hbq V2 Z))
/-- Undo the third line: subtract the controls ... -/
def off2a (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (W2 Z : List Bool) : List Bool :=
  gather (fun _ z => z) (controlsAt q b hb hbq) W2 Z Z.length
def t (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  digits subRule 0 (V2.zip (off2a q b hb hbq W2 Z))
/-- ... and add back twice the masked digits of `W₁`. -/
def off2b (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  gather (fun x z => x && z) (maskShift q b hb hbq) (w1 q b hb hbq V2 W2 Z) Z Z.length
def v1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  digits addRule 0 ((t q b hb hbq V2 W2 Z).zip (off2b q b hb hbq V2 W2 Z))
/-- Undo the second line: subtract the parities of `V₁`. -/
def off3 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  gather (fun x _ => x) (parity q b hb hbq) (v1 q b hb hbq V2 W2 Z) Z Z.length
def w (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  digits subRule 0 ((w1 q b hb hbq V2 W2 Z).zip (off3 q b hb hbq V2 W2 Z))
/-- Undo the first line: subtract twice the masked digits of `W`. -/
def off4 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  gather (fun x z => x && z) (maskShift q b hb hbq) (w q b hb hbq V2 W2 Z) Z Z.length
def v (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool) : List Bool :=
  digits subRule 0 ((v1 q b hb hbq V2 W2 Z).zip (off4 q b hb hbq V2 W2 Z))

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool)
variable (hV : V2.length = Z.length * q) (hW : W2.length = Z.length * b)

include hV hW in
theorem lengths :
    (off1 q b hb hbq V2 Z).length = Z.length * b ∧ (w1 q b hb hbq V2 W2 Z).length = Z.length * b ∧
    (off2a q b hb hbq W2 Z).length = Z.length * q ∧ (t q b hb hbq V2 W2 Z).length = Z.length * q ∧
    (off2b q b hb hbq V2 W2 Z).length = Z.length * q ∧ (v1 q b hb hbq V2 W2 Z).length = Z.length * q ∧
    (off3 q b hb hbq V2 W2 Z).length = Z.length * b ∧ (w q b hb hbq V2 W2 Z).length = Z.length * b ∧
    (off4 q b hb hbq V2 W2 Z).length = Z.length * q ∧ (v q b hb hbq V2 W2 Z).length = Z.length * q := by
  have h1 : (off1 q b hb hbq V2 Z).length = Z.length * b := Gather.gather_length _ _ _ _ _
  have h2 : (w1 q b hb hbq V2 W2 Z).length = Z.length * b := by
    simp [w1, ColumnTransducer.digits_length, List.length_zip, hW, h1]
  have h3 : (off2a q b hb hbq W2 Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h4 : (t q b hb hbq V2 W2 Z).length = Z.length * q := by
    simp [t, ColumnTransducer.digits_length, List.length_zip, hV, h3]
  have h5 : (off2b q b hb hbq V2 W2 Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h6 : (v1 q b hb hbq V2 W2 Z).length = Z.length * q := by
    simp [v1, ColumnTransducer.digits_length, List.length_zip, h4, h5]
  have h7 : (off3 q b hb hbq V2 W2 Z).length = Z.length * b := Gather.gather_length _ _ _ _ _
  have h8 : (w q b hb hbq V2 W2 Z).length = Z.length * b := by
    simp [w, ColumnTransducer.digits_length, List.length_zip, h2, h7]
  have h9 : (off4 q b hb hbq V2 W2 Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h10 : (v q b hb hbq V2 W2 Z).length = Z.length * q := by
    simp [v, ColumnTransducer.digits_length, List.length_zip, h6, h9]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Lists

section Machine

def I1 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 1 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else 8
  invFun := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def I2a : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 0 else if i = 4 then 4 else if i = 5 then 3 else if i = 6 then 5 else if i = 7 then 6 else 8
  invFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 5 else if i = 4 then 4 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def I2b : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 0 else if i = 6 then 1 else if i = 7 then 6 else 8
  invFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 1 else if i = 3 then 0 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 7 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def I3 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 3 else if i = 4 then 6 else if i = 5 then 0 else if i = 6 then 1 else if i = 7 then 4 else 8
  invFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 7 else if i = 5 then 0 else if i = 6 then 4 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def I4 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 6 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 5 else if i = 4 then 8 else if i = 5 then 0 else if i = 6 then 1 else if i = 7 then 3 else 4
  invFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 1 else if i = 3 then 7 else if i = 4 then 8 else if i = 5 then 3 else if i = 6 then 0 else if i = 7 then 2 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem I1_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f0 f2 f7 f1 f3 p0 p2 p7 p1 p3).append
      (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8, fun i => if i = 0 then f4 else if i = 1 then f5 else if i = 2 then f6 else f8⟩ : Tapes 4 a)).reindex I1 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank I1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem I2a_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f1 f2 f7 f0 f4 p1 p2 p7 p0 p4).append
      (⟨fun i => if i = 0 then p3 else if i = 1 then p5 else if i = 2 then p6 else p8, fun i => if i = 0 then f3 else if i = 1 then f5 else if i = 2 then f6 else f8⟩ : Tapes 4 a)).reindex I2a = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank I2a
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem I2b_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f3 f2 f7 f4 f5 p3 p2 p7 p4 p5).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p6 else p8, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f6 else f8⟩ : Tapes 4 a)).reindex I2b = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank I2b
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem I3_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f5 f2 f7 f3 f6 p5 p2 p7 p3 p6).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p4 else p8, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f4 else f8⟩ : Tapes 4 a)).reindex I3 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank I3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem I4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f6 f2 f7 f5 f8 p6 p2 p7 p5 p8).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex I4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank I4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (n : ℕ)

def line1 (a : ℕ) := reindex (extend (PackedLine.program (fun x z => xor x z) (parity q b hb hbq) n addRule a) 4) I1
def line2a (a : ℕ) := reindex (extend (PackedLine.program (fun _ z => z) (controlsAt q b hb hbq) n subRule a) 4) I2a
def line2b (a : ℕ) := reindex (extend (PackedLine.program (fun x z => x && z) (maskShift q b hb hbq) n addRule a) 4) I2b
def line3 (a : ℕ) := reindex (extend (PackedLine.program (fun x _ => x) (parity q b hb hbq) n subRule a) 4) I3
def line4 (a : ℕ) := reindex (extend (PackedLine.program (fun x z => x && z) (maskShift q b hb hbq) n subRule a) 4) I4

/-- The inverse program: the five lines in sequence. -/
def program (a : ℕ) := seq (seq (seq (seq (line1 q b hb hbq n a) (line2a q b hb hbq n a))
  (line2b q b hb hbq n a)) (line3 q b hb hbq n a)) (line4 q b hb hbq n a)

/-- The total cost. -/
def cost : ℕ :=
  PackedLine.lineCost (parity q b hb hbq) n (n * b) + 1 +
  PackedLine.lineCost (controlsAt q b hb hbq) n (n * q) + 1 +
  PackedLine.lineCost (maskShift q b hb hbq) n (n * q) + 1 +
  PackedLine.lineCost (parity q b hb hbq) n (n * b) + 1 +
  PackedLine.lineCost (maskShift q b hb hbq) n (n * q)

variable (V2 W2 Z : List Bool) (f g z : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ)

/-- The input bank: the three words, everything else blank. -/
def input : Tapes 9 a :=
  bank (putWord f p0 (V2.map bitSymbol)) (putWord g p1 (W2.map bitSymbol)) (putWord z p2 (Z.map bitSymbol))
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank)
    p0 p1 p2 p3 p4 p5 p6 p7 p8

/-- The output bank: the intermediate and recovered words on their own tapes. -/
def output : Tapes 9 a :=
  bank (putWord f p0 (V2.map bitSymbol)) (putWord g p1 (W2.map bitSymbol)) (putWord z p2 (Z.map bitSymbol))
    (putWord (fun _ => blank) p3 ((w1 q b hb hbq V2 W2 Z).map bitSymbol))
    (putWord (fun _ => blank) p4 ((t q b hb hbq V2 W2 Z).map bitSymbol))
    (putWord (fun _ => blank) p5 ((v1 q b hb hbq V2 W2 Z).map bitSymbol))
    (putWord (fun _ => blank) p6 ((w q b hb hbq V2 W2 Z).map bitSymbol))
    (fun _ => blank)
    (putWord (fun _ => blank) p8 ((v q b hb hbq V2 W2 Z).map bitSymbol))
    p0 p1 p2 p3 p4 p5 p6 p7 p8

/-- The inverse program's contract. -/
theorem inverse_hoare (hV : V2.length = Z.length * q) (hW : W2.length = Z.length * b)
    (hf : f (p0 - 1) = blank) (hf' : f (p0 + V2.length) = blank) (hg : g (p1 - 1) = blank)
    (hg' : g (p1 + W2.length) = blank) (hz : z (p2 - 1) = blank) :
    HoareTime (program q b hb hbq Z.length a)
      (fun x => x = input V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
      (fun x => x = output q b hb hbq V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
      (cost q b hb hbq Z.length) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V2 W2 Z hV hW
  set W1 := w1 q b hb hbq V2 W2 Z
  set T := t q b hb hbq V2 W2 Z
  set V1 := v1 q b hb hbq V2 W2 Z
  set Wd := w q b hb hbq V2 W2 Z
  set Vd := v q b hb hbq V2 W2 Z
  -- line 1: W₁ := W₂ + toggled parities of V₂
  have h1 := hoare_place (PackedLine.line_hoare (fun x z => xor x z) (parity q b hb hbq) addRule V2 Z W2
    f z g p0 p2 p7 p1 p3 (by simp only [parity]; rw [hV]) (by simp only [parity]; exact hW)
    hf hz hg hg') I1
    (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then (fun _ => blank) else if i = 1 then (fun _ => blank) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I1_bank, I1_bank] at h1
  -- line 2a: T := V₂ − controls
  have h2 := hoare_place (PackedLine.line_hoare (fun _ z => z) (controlsAt q b hb hbq) subRule W2 Z V2
    g z f p1 p2 p7 p0 p4
    (by simp only [controlsAt, mul_one]; rw [hW]; exact Nat.le_mul_of_pos_right _ hb)
    (by simp only [controlsAt]; exact hV) hg hz hf hf') I2a
    (⟨fun i => if i = 0 then p3 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord (fun _ => blank) p3 (W1.map bitSymbol) else if i = 1 then (fun _ => blank)
        else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I2a_bank, I2a_bank] at h2
  -- line 2b: V₁ := T + masked digits of W₁
  have h3 := hoare_place (PackedLine.line_hoare (fun x z => x && z) (maskShift q b hb hbq) addRule W1 Z T
    (fun _ => blank) z (fun _ => blank) p3 p2 p7 p4 p5 (by simp only [maskShift]; rw [l2])
    (by simp only [maskShift]; exact l4) rfl hz rfl rfl) I2b
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I2b_bank, I2b_bank] at h3
  -- line 3: W := W₁ − parities of V₁
  have h4 := hoare_place (PackedLine.line_hoare (fun x _ => x) (parity q b hb hbq) subRule V1 Z W1
    (fun _ => blank) z (fun _ => blank) p5 p2 p7 p3 p6 (by simp only [parity]; rw [l6])
    (by simp only [parity]; exact l2) rfl hz rfl rfl) I3
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p4 else p8,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p4 (T.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I3_bank, I3_bank] at h4
  -- line 4: V := V₁ − masked digits of W
  have h5 := hoare_place (PackedLine.line_hoare (fun x z => x && z) (maskShift q b hb hbq) subRule Wd Z V1
    (fun _ => blank) z (fun _ => blank) p6 p2 p7 p5 p8 (by simp only [maskShift]; rw [l8])
    (by simp only [maskShift]; exact l6) rfl hz rfl rfl) I4
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (W1.map bitSymbol)
        else putWord (fun _ => blank) p4 (T.map bitSymbol)⟩ : Tapes 4 a)
  rw [I4_bank, I4_bank] at h5
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  refine hall.consequence (fun x hx => by rw [hx]; rfl) (fun x hx => by rw [hx]; rfl) ?_
  simp only [cost, hV, hW, l2, l4, l6]
  omega

end Machine

end IntegerMultBounds.Machine.PackedInverse

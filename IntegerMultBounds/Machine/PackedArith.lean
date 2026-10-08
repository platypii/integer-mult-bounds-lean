import IntegerMultBounds.Machine.PackedLine

/-! The forward packed program of the compact-control address arithmetic on
nine tapes, for digit widths `q` and `b` with `b + 1 ≤ q` and `n` digits:
the four packed updates of `packedEarly` with the radices `2^q` and `2^b`,
each a line gathering its offset from the current words under the control
word and combining by a modular column transducer into a fresh word. The
input words and the control are preserved, the offset scratch is blank again,
and the final words sit on their own tapes with every head at its origin. -/

namespace IntegerMultBounds.Machine.PackedArith

variable {a : ℕ}

open ColumnTransducer (Rule addRule subRule digits)
open Gather (Shape gather)

/-- The nine-tape bank: `V`, `W`, `Z`, `V₁`, `W₁`, `V₂`, `W₂`, offset scratch, `T₁`. -/
def bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) : Tapes 9 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7 else p8,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3
    else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7 else f8⟩

section Shapes

/-- A `b`-bit block masked by the control and shifted up by one, at stride `q`. -/
def maskShift (q b : ℕ) (_hb : 1 ≤ b) (hbq : b + 1 ≤ q) : Shape :=
  ⟨b, 0, b, q, 1, by omega, by omega⟩

/-- The parity of each `q`-bit block, at stride `b`. -/
def parity (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) : Shape := ⟨q, 0, 1, b, 0, by omega, by omega⟩

/-- The control bits themselves, at stride `q`. -/
def controlsAt (q b : ℕ) (_hb : 1 ≤ b) (hbq : b + 1 ≤ q) : Shape :=
  ⟨1, 0, 1, q, 0, by omega, by omega⟩

end Shapes

section Lists

/-- The first line's offset: `2 z_i w_i` at stride `q`. -/
def off1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (W Z : List Bool) : List Bool :=
  gather (fun x z => x && z) (maskShift q b hb hbq) W Z Z.length
def v1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  digits addRule 0 (V.zip (off1 q b hb hbq W Z))
/-- The second line's offset: the parity of each digit of `V₁` at stride `b`. -/
def off2 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  gather (fun x _ => x) (parity q b hb hbq) (v1 q b hb hbq V W Z) Z Z.length
def w1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  digits addRule 0 (W.zip (off2 q b hb hbq V W Z))
/-- The third line adds the controls at stride `q` ... -/
def off3a (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (W Z : List Bool) : List Bool :=
  gather (fun _ z => z) (controlsAt q b hb hbq) W Z Z.length
def t1 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  digits addRule 0 ((v1 q b hb hbq V W Z).zip (off3a q b hb hbq W Z))
/-- ... and subtracts twice the masked digits of `W₁`. -/
def off3b (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  gather (fun x z => x && z) (maskShift q b hb hbq) (w1 q b hb hbq V W Z) Z Z.length
def v2 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  digits subRule 0 ((t1 q b hb hbq V W Z).zip (off3b q b hb hbq V W Z))
/-- The fourth line subtracts the toggled parities of `V₂` at stride `b`. -/
def off4 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  gather (fun x z => xor x z) (parity q b hb hbq) (v2 q b hb hbq V W Z) Z Z.length
def w2 (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool) : List Bool :=
  digits subRule 0 ((w1 q b hb hbq V W Z).zip (off4 q b hb hbq V W Z))

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V W Z : List Bool)
variable (hV : V.length = Z.length * q) (hW : W.length = Z.length * b)

include hV hW in
theorem lengths :
    (off1 q b hb hbq W Z).length = Z.length * q ∧ (v1 q b hb hbq V W Z).length = Z.length * q ∧
    (off2 q b hb hbq V W Z).length = Z.length * b ∧ (w1 q b hb hbq V W Z).length = Z.length * b ∧
    (off3a q b hb hbq W Z).length = Z.length * q ∧ (t1 q b hb hbq V W Z).length = Z.length * q ∧
    (off3b q b hb hbq V W Z).length = Z.length * q ∧ (v2 q b hb hbq V W Z).length = Z.length * q ∧
    (off4 q b hb hbq V W Z).length = Z.length * b ∧ (w2 q b hb hbq V W Z).length = Z.length * b := by
  have h1 : (off1 q b hb hbq W Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h2 : (v1 q b hb hbq V W Z).length = Z.length * q := by
    simp [v1, ColumnTransducer.digits_length, List.length_zip, hV, h1]
  have h3 : (off2 q b hb hbq V W Z).length = Z.length * b := Gather.gather_length _ _ _ _ _
  have h4 : (w1 q b hb hbq V W Z).length = Z.length * b := by
    simp [w1, ColumnTransducer.digits_length, List.length_zip, hW, h3]
  have h5 : (off3a q b hb hbq W Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h6 : (t1 q b hb hbq V W Z).length = Z.length * q := by
    simp [t1, ColumnTransducer.digits_length, List.length_zip, h2, h5]
  have h7 : (off3b q b hb hbq V W Z).length = Z.length * q := Gather.gather_length _ _ _ _ _
  have h8 : (v2 q b hb hbq V W Z).length = Z.length * q := by
    simp [v2, ColumnTransducer.digits_length, List.length_zip, h6, h7]
  have h9 : (off4 q b hb hbq V W Z).length = Z.length * b := Gather.gather_length _ _ _ _ _
  have h10 : (w2 q b hb hbq V W Z).length = Z.length * b := by
    simp [w2, ColumnTransducer.digits_length, List.length_zip, h4, h9]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Lists

section Machine

def L1 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 0 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else 8
  invFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def L2 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 1 else if i = 4 then 4 else if i = 5 then 0 else if i = 6 then 5 else if i = 7 then 6 else 8
  invFun := fun i => if i = 0 then 5 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 0 else if i = 4 then 4 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def L3a : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 3 else if i = 4 then 8 else if i = 5 then 0 else if i = 6 then 4 else if i = 7 then 5 else 6
  invFun := fun i => if i = 0 then 5 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 6 else if i = 5 then 7 else if i = 6 then 8 else if i = 7 then 2 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def L3b : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 8 else if i = 4 then 5 else if i = 5 then 0 else if i = 6 then 1 else if i = 7 then 3 else 6
  invFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 1 else if i = 3 then 7 else if i = 4 then 0 else if i = 5 then 4 else if i = 6 then 8 else if i = 7 then 2 else 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def L4 : Fin (5 + 4) ≃ Fin 9 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 2 else if i = 2 then 7 else if i = 3 then 4 else if i = 4 then 6 else if i = 5 then 0 else if i = 6 then 1 else if i = 7 then 3 else 8
  invFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 1 else if i = 3 then 7 else if i = 4 then 3 else if i = 5 then 0 else if i = 6 then 4 else if i = 7 then 2 else 8
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem L1_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f1 f2 f7 f0 f3 p1 p2 p7 p0 p3).append
      (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8, fun i => if i = 0 then f4 else if i = 1 then f5 else if i = 2 then f6 else f8⟩ : Tapes 4 a)).reindex L1 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank L1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem L2_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f3 f2 f7 f1 f4 p3 p2 p7 p1 p4).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p5 else if i = 2 then p6 else p8, fun i => if i = 0 then f0 else if i = 1 then f5 else if i = 2 then f6 else f8⟩ : Tapes 4 a)).reindex L2 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank L2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem L3a_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f1 f2 f7 f3 f8 p1 p2 p7 p3 p8).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p4 else if i = 2 then p5 else p6, fun i => if i = 0 then f0 else if i = 1 then f4 else if i = 2 then f5 else f6⟩ : Tapes 4 a)).reindex L3a = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank L3a
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem L3b_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f4 f2 f7 f8 f5 p4 p2 p7 p8 p5).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p6, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f6⟩ : Tapes 4 a)).reindex L3b = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank L3b
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem L4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) :
    ((PackedLine.bank f5 f2 f7 f4 f6 p5 p2 p7 p4 p6).append
      (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p8, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f8⟩ : Tapes 4 a)).reindex L4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 p0 p1 p2 p3 p4 p5 p6 p7 p8 := by
  unfold Tapes.reindex Tapes.append PackedLine.bank bank L4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (n : ℕ)

def line1 (a : ℕ) := reindex (extend (PackedLine.program (fun x z => x && z) (maskShift q b hb hbq) n addRule a) 4) L1
def line2 (a : ℕ) := reindex (extend (PackedLine.program (fun x _ => x) (parity q b hb hbq) n addRule a) 4) L2
def line3a (a : ℕ) := reindex (extend (PackedLine.program (fun _ z => z) (controlsAt q b hb hbq) n addRule a) 4) L3a
def line3b (a : ℕ) := reindex (extend (PackedLine.program (fun x z => x && z) (maskShift q b hb hbq) n subRule a) 4) L3b
def line4 (a : ℕ) := reindex (extend (PackedLine.program (fun x z => xor x z) (parity q b hb hbq) n subRule a) 4) L4

/-- The forward program: the five lines in sequence. -/
def program (a : ℕ) := seq (seq (seq (seq (line1 q b hb hbq n a) (line2 q b hb hbq n a))
  (line3a q b hb hbq n a)) (line3b q b hb hbq n a)) (line4 q b hb hbq n a)

/-- The total cost. -/
def cost : ℕ :=
  PackedLine.lineCost (maskShift q b hb hbq) n (n * q) + 1 +
  PackedLine.lineCost (parity q b hb hbq) n (n * b) + 1 +
  PackedLine.lineCost (controlsAt q b hb hbq) n (n * q) + 1 +
  PackedLine.lineCost (maskShift q b hb hbq) n (n * q) + 1 +
  PackedLine.lineCost (parity q b hb hbq) n (n * b)

variable (V W Z : List Bool) (f g z : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ)

/-- The input bank: the three words, everything else blank. -/
def input : Tapes 9 a :=
  bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol)) (putWord z p2 (Z.map bitSymbol))
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank) (fun _ => blank)
    p0 p1 p2 p3 p4 p5 p6 p7 p8

/-- The output bank: the intermediate and final words on their own tapes. -/
def output : Tapes 9 a :=
  bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol)) (putWord z p2 (Z.map bitSymbol))
    (putWord (fun _ => blank) p3 ((v1 q b hb hbq V W Z).map bitSymbol))
    (putWord (fun _ => blank) p4 ((w1 q b hb hbq V W Z).map bitSymbol))
    (putWord (fun _ => blank) p5 ((v2 q b hb hbq V W Z).map bitSymbol))
    (putWord (fun _ => blank) p6 ((w2 q b hb hbq V W Z).map bitSymbol))
    (fun _ => blank)
    (putWord (fun _ => blank) p8 ((t1 q b hb hbq V W Z).map bitSymbol))
    p0 p1 p2 p3 p4 p5 p6 p7 p8

/-- The forward program's contract. -/
theorem forward_hoare (hV : V.length = Z.length * q) (hW : W.length = Z.length * b)
    (hf : f (p0 - 1) = blank) (hf' : f (p0 + V.length) = blank) (hg : g (p1 - 1) = blank)
    (hg' : g (p1 + W.length) = blank) (hz : z (p2 - 1) = blank) :
    HoareTime (program q b hb hbq Z.length a)
      (fun v => v = input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
      (fun v => v = output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8)
      (cost q b hb hbq Z.length) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V W Z hV hW
  set O1 := off1 q b hb hbq W Z
  set V1 := v1 q b hb hbq V W Z
  set O2 := off2 q b hb hbq V W Z
  set W1 := w1 q b hb hbq V W Z
  set O3a := off3a q b hb hbq W Z
  set T1 := t1 q b hb hbq V W Z
  set O3b := off3b q b hb hbq V W Z
  set V2 := v2 q b hb hbq V W Z
  set O4 := off4 q b hb hbq V W Z
  set W2 := w2 q b hb hbq V W Z
  -- line 1: V₁ := V + off1
  have h1 := hoare_place (PackedLine.line_hoare (fun x z => x && z) (maskShift q b hb hbq) addRule W Z V
    g z f p1 p2 p7 p0 p3 (by simp only [maskShift]; rw [hW]) (by simp only [maskShift]; exact hV)
    hg hz hf hf') L1
    (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then (fun _ => blank) else if i = 1 then (fun _ => blank) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L1_bank, L1_bank] at h1
  -- line 2: W₁ := W + off2
  have h2 := hoare_place (PackedLine.line_hoare (fun x _ => x) (parity q b hb hbq) addRule V1 Z W
    (fun _ => blank) z g p3 p2 p7 p1 p4 (by simp only [parity]; rw [l2]) (by simp only [parity]; exact hW)
    rfl hz hg hg') L2
    (⟨fun i => if i = 0 then p0 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol) else if i = 1 then (fun _ => blank)
        else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L2_bank, L2_bank] at h2
  -- line 3a: T₁ := V₁ + controls
  have h3 := hoare_place (PackedLine.line_hoare (fun _ z => z) (controlsAt q b hb hbq) addRule W Z V1
    g z (fun _ => blank) p1 p2 p7 p3 p8
    (by simp only [controlsAt, mul_one]; rw [hW]; exact Nat.le_mul_of_pos_right _ hb)
    (by simp only [controlsAt]; exact l2) hg hz rfl rfl) L3a
    (⟨fun i => if i = 0 then p0 else if i = 1 then p4 else if i = 2 then p5 else p6,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord (fun _ => blank) p4 (W1.map bitSymbol) else if i = 2 then (fun _ => blank)
        else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L3a_bank, L3a_bank] at h3
  -- line 3b: V₂ := T₁ − off3b
  have h4 := hoare_place (PackedLine.line_hoare (fun x z => x && z) (maskShift q b hb hbq) subRule W1 Z T1
    (fun _ => blank) z (fun _ => blank) p4 p2 p7 p8 p5 (by simp only [maskShift]; rw [l4])
    (by simp only [maskShift]; exact l6) rfl hz rfl rfl) L3b
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p6,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord g p1 (W.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (V1.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L3b_bank, L3b_bank] at h4
  -- line 4: W₂ := W₁ − off4
  have h5 := hoare_place (PackedLine.line_hoare (fun x z => xor x z) (parity q b hb hbq) subRule V2 Z W1
    (fun _ => blank) z (fun _ => blank) p5 p2 p7 p4 p6 (by simp only [parity]; rw [l8])
    (by simp only [parity]; exact l4) rfl hz rfl rfl) L4
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p8,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord g p1 (W.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (V1.map bitSymbol)
        else putWord (fun _ => blank) p8 (T1.map bitSymbol)⟩ : Tapes 4 a)
  rw [L4_bank, L4_bank] at h5
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  refine hall.consequence (fun v hv => by rw [hv]; rfl) (fun v hv => by rw [hv]; rfl) ?_
  simp only [cost, hV, hW, l2, l4, l6]
  omega

end Machine

end IntegerMultBounds.Machine.PackedArith

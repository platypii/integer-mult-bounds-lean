import IntegerMultBounds.Machine.GuardTest

/-! The guard test of the compact-control repair on seven tapes: for each
`q`-bit block of the first word its upper `q - 1` bits are compared with two
constant words, and for each `b`-bit block of the second word the block is
compared with a third constant, each comparison appending one flag bit; the
flag word then records every failed guard. Everything is unrolled into
finite control with linear cost; the words and constants are preserved. -/

namespace IntegerMultBounds.Machine.GuardGadget

variable {a : ℕ}

open GuardTest (cmpCell flagCell orderAfter ordSymbol cmpCells_hoare flagCell_hoare)
open Gather (field)

/-- The seven-tape bank: `V`, `W`, the three constants, the order cell, the flag word. -/
def bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) : Tapes 7 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else p6,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3
    else if i = 4 then f4 else if i = 5 then f5 else f6⟩

def cmpV1 : Fin (3 + 4) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 5 else if i = 3 then 1 else if i = 4 then 3 else if i = 5 then 4 else 6
  invFun := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 2 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cmpV2 : Fin (3 + 4) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 5 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 4 else 6
  invFun := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 1 else if i = 4 then 5 else if i = 5 then 2 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cmpW : Fin (3 + 4) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 0 else if i = 4 then 2 else if i = 5 then 3 else 6
  invFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 1 else if i = 5 then 2 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def flagP : Fin (2 + 5) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 6 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else 4
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 6 else if i = 5 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def oneV : Fin (1 + 6) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 6
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def oneC1 : Fin (1 + 6) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 6
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def oneC2 : Fin (1 + 6) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 4 else if i = 5 then 5 else 6
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else if i = 4 then 4 else if i = 5 then 5 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def oneC3 : Fin (1 + 6) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 5 else 6
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 0 else if i = 5 then 5 else 6
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def oneF : Fin (1 + 6) ≃ Fin 7 where
  toFun := fun i => if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else 5
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem cmpV1_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((GuardTest.bank f0 f2 f5 p0 p2 p5).append (⟨fun i => if i = 0 then p1 else if i = 1 then p3 else if i = 2 then p4 else p6, fun i => if i = 0 then f1 else if i = 1 then f3 else if i = 2 then f4 else f6⟩ : Tapes 4 a)).reindex cmpV1 = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append GuardTest.bank bank cmpV1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem cmpV2_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((GuardTest.bank f0 f3 f5 p0 p3 p5).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p4 else p6, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f4 else f6⟩ : Tapes 4 a)).reindex cmpV2 = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append GuardTest.bank bank cmpV2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem cmpW_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((GuardTest.bank f1 f4 f5 p1 p4 p5).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else p6, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else f6⟩ : Tapes 4 a)).reindex cmpW = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append GuardTest.bank bank cmpW
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem flagP_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((GuardTest.bank2 f5 f6 p5 p6).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩ : Tapes 5 a)).reindex flagP = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append GuardTest.bank2 bank flagP
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem oneV_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4 else if i = 4 then p5 else p6, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else if i = 3 then f4 else if i = 4 then f5 else f6⟩ : Tapes 6 a)).reindex oneV = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append  bank oneV
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem oneC1_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else if i = 3 then p4 else if i = 4 then p5 else p6, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else if i = 3 then f4 else if i = 4 then f5 else f6⟩ : Tapes 6 a)).reindex oneC1 = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append  bank oneC1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem oneC2_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p4 else if i = 4 then p5 else p6, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f4 else if i = 4 then f5 else f6⟩ : Tapes 6 a)).reindex oneC2 = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append  bank oneC2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem oneC3_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((⟨fun _ => p4, fun _ => f4⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p5 else p6, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f5 else f6⟩ : Tapes 6 a)).reindex oneC3 = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append  bank oneC3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem oneF_bank (f0 f1 f2 f3 f4 f5 f6 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 : ℤ) :
    ((⟨fun _ => p6, fun _ => f6⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else p5, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else f5⟩ : Tapes 6 a)).reindex oneF = bank f0 f1 f2 f3 f4 f5 f6 p0 p1 p2 p3 p4 p5 p6 := by
  unfold Tapes.reindex Tapes.append  bank oneF
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def cmpV1Part (d : ℕ) (a : ℕ) := reindex (extend (iterate (cmpCell a) d) 4) cmpV1
def cmpV2Part (d : ℕ) (a : ℕ) := reindex (extend (iterate (cmpCell a) d) 4) cmpV2
def cmpWPart (d : ℕ) (a : ℕ) := reindex (extend (iterate (cmpCell a) d) 4) cmpW
def flagLt (a : ℕ) := reindex (extend (flagCell .lt a) 5) flagP
def flagGt (a : ℕ) := reindex (extend (flagCell .gt a) 5) flagP
def stepV (a : ℕ) := reindex (extend (StepRight.program (a := a)) 6) oneV
def backV (d : ℕ) (a : ℕ) := reindex (extend (iterate (StepLeft.program (a := a)) d) 6) oneV
def retC1 (a : ℕ) := reindex (extend (ReturnOrigin.program (a := a)) 6) oneC1
def retC2 (a : ℕ) := reindex (extend (ReturnOrigin.program (a := a)) 6) oneC2
def retC3 (a : ℕ) := reindex (extend (ReturnOrigin.program (a := a)) 6) oneC3

/-- One block of the first word: skip the low bit, compare with the first
constant (flag "smaller"), back up, compare with the second (flag "larger"). -/
def digitV (q : ℕ) (a : ℕ) :=
  seq (seq (seq (seq (seq (seq (seq (stepV a) (cmpV1Part (q - 1) a)) (flagLt a)) (backV (q - 1) a))
    (retC1 a)) (cmpV2Part (q - 1) a)) (flagGt a)) (retC2 a)

/-- One block of the second word: compare with the third constant (flag "larger"). -/
def digitW (b : ℕ) (a : ℕ) := seq (seq (cmpWPart b a) (flagGt a)) (retC3 a)

/-- The whole test over `n` blocks of each word. -/
def program (q b n : ℕ) (a : ℕ) := seq (iterate (digitV q a) n) (iterate (digitW b a) n)

section Lists

/-- The two flags of a block of the first word. -/
def flagsV (q : ℕ) (V C1 C2 : List Bool) (i : ℕ) : List Bool :=
  [decide (orderAfter .eq V C1 (i * q + 1) (q - 1) = .lt),
   decide (orderAfter .eq V C2 (i * q + 1) (q - 1) = .gt)]

/-- The flag of a block of the second word. -/
def flagsW (b : ℕ) (W C3 : List Bool) (i : ℕ) : List Bool :=
  [decide (orderAfter .eq W C3 (i * b) b = .gt)]

/-- The flag word after `i` blocks of the first word. -/
def flagWordV (q : ℕ) (V C1 C2 : List Bool) : ℕ → List Bool
  | 0 => []
  | i + 1 => flagWordV q V C1 C2 i ++ flagsV q V C1 C2 i

/-- The flag word after all blocks of the first word and `i` of the second. -/
def flagWordW (q b n : ℕ) (V W C1 C2 C3 : List Bool) : ℕ → List Bool
  | 0 => flagWordV q V C1 C2 n
  | i + 1 => flagWordW q b n V W C1 C2 C3 i ++ flagsW b W C3 i

theorem flagWordV_length (q : ℕ) (V C1 C2 : List Bool) (i : ℕ) :
    (flagWordV q V C1 C2 i).length = 2 * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [flagWordV, flagsV, ih]; ring

theorem flagWordW_length (q b n : ℕ) (V W C1 C2 C3 : List Bool) (i : ℕ) :
    (flagWordW q b n V W C1 C2 C3 i).length = 2 * n + i := by
  induction i with
  | zero => simp [flagWordW, flagWordV_length]
  | succ i ih => simp [flagWordW, flagsW, ih]; ring

end Lists

section Machine

variable (q b n : ℕ) (V W C1 C2 C3 : List Bool) (f g c1 c2 c3 : ℤ → Fin (a + 4))
  (p0 p1 p2 p3 p4 p5 p6 : ℤ)

/-- The blank order cell as an updated cell. -/
theorem blank_eq_update (po : ℤ) :
    (fun _ => (blank : Fin (a + 4))) = Function.update (fun _ => blank) po (ordSymbol .eq) := by
  funext j; by_cases hj : j = po <;> simp [hj, ordSymbol]

/-- The bank after `i` blocks of the first word. -/
def stateV (i : ℕ) : Tapes 7 a :=
  bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol))
    (putWord c1 p2 (C1.map bitSymbol)) (putWord c2 p3 (C2.map bitSymbol))
    (putWord c3 p4 (C3.map bitSymbol)) (fun _ => blank)
    (putWord (fun _ => blank) p6 ((flagWordV q V C1 C2 i).map bitSymbol))
    (p0 + i * q) p1 p2 p3 p4 p5 (p6 + 2 * i)

/-- The bank after all blocks of the first word and `i` of the second. -/
def stateW (i : ℕ) : Tapes 7 a :=
  bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol))
    (putWord c1 p2 (C1.map bitSymbol)) (putWord c2 p3 (C2.map bitSymbol))
    (putWord c3 p4 (C3.map bitSymbol)) (fun _ => blank)
    (putWord (fun _ => blank) p6 ((flagWordW q b n V W C1 C2 C3 i).map bitSymbol))
    (p0 + n * q) (p1 + i * b) p2 p3 p4 p5 (p6 + 2 * n + i)

/-- Moving a head left `k` cells. -/
theorem backV_hoare (k : ℕ) (T1 T2 T3 T4 T5 T6 : ℤ → Fin (a + 4)) (f0 : ℤ → Fin (a + 4))
    (x p1 p2 p3 p4 p5 p6 : ℤ) :
    HoareTime (backV k a) (fun v => v = bank f0 T1 T2 T3 T4 T5 T6 x p1 p2 p3 p4 p5 p6)
      (fun v => v = bank f0 T1 T2 T3 T4 T5 T6 (x - k) p1 p2 p3 p4 p5 p6) (k * (1 + 1)) := by
  have hit := iterate_hoare (StepLeft.program (a := a)) k
    (fun j => (StepLeft.cfg f0 (x - j) 0).tapes) 1 (fun j hj => by
      have h := StepLeft.step_hoare f0 (x - j)
      refine h.consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
      rw [hv]; congr 1; push_cast; ring)
  have hp := hoare_place hit oneV
    (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4
        else if i = 4 then p5 else p6,
      fun i => if i = 0 then T1 else if i = 1 then T2 else if i = 2 then T3 else if i = 3 then T4
        else if i = 4 then T5 else T6⟩ : Tapes 6 a)
  simp only [StepLeft.cfg, Config.tapes, Nat.cast_zero, sub_zero] at hp
  rwa [oneV_bank, oneV_bank] at hp

theorem update_blank_blank (po : ℤ) :
    Function.update (fun _ => (blank : Fin (a + 4))) po blank = fun _ => blank := by
  funext j; by_cases hj : j = po <;> simp [hj]

variable (hV : V.length = n * q) (hW : W.length = n * b) (hq : 1 ≤ q)
  (hC1 : C1.length = q - 1) (hC2 : C2.length = q - 1) (hC3 : C3.length = b)
  (hc1 : c1 (p2 - 1) = blank) (hc2 : c2 (p3 - 1) = blank) (hc3 : c3 (p4 - 1) = blank)

/-- The cost of one block of the first word. -/
def digitVCost (q : ℕ) : ℕ :=
  1 + 1 + (q - 1) * (1 + 1) + 1 + 1 + 1 + (q - 1) * (1 + 1) + 1 + ((q - 1) + 2) + 1 +
    (q - 1) * (1 + 1) + 1 + 1 + 1 + ((q - 1) + 2)

/-- The cost of one block of the second word. -/
def digitWCost (b : ℕ) : ℕ := b * (1 + 1) + 1 + 1 + 1 + (b + 2)

include hV hq hC1 hC2 hc1 hc2 in
theorem digitV_hoare (i : ℕ) (hi : i < n) :
    HoareTime (digitV q a) (fun v => v = stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 i)
      (fun v => v = stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 (i + 1))
      (digitVCost q) := by
  set X := putWord f p0 (V.map bitSymbol)
  set Y := putWord g p1 (W.map bitSymbol)
  set K1 := putWord c1 p2 (C1.map bitSymbol)
  set K2 := putWord c2 p3 (C2.map bitSymbol)
  set K3 := putWord c3 p4 (C3.map bitSymbol)
  set Fw := flagWordV q V C1 C2 i
  set o1 := orderAfter .eq V C1 (i * q + 1) (q - 1)
  set o2 := orderAfter .eq V C2 (i * q + 1) (q - 1)
  have hFw : (Fw.map (bitSymbol (a := a))).length = 2 * i := by simp [Fw, flagWordV_length]
  -- skip the low bit
  have s1 := hoare_place (StepRight.step_hoare (a := a) X (p0 + i * q)) oneV
    (⟨fun j => if j = 0 then p1 else if j = 1 then p2 else if j = 2 then p3 else if j = 3 then p4
        else if j = 4 then p5 else p6 + 2 * i,
      fun j => if j = 0 then Y else if j = 1 then K1 else if j = 2 then K2 else if j = 3 then K3
        else if j = 4 then (fun _ => blank) else putWord (fun _ => blank) p6 (Fw.map bitSymbol)⟩ :
      Tapes 6 a)
  simp only [StepRight.cfg, Config.tapes] at s1
  rw [oneV_bank, oneV_bank] at s1
  have hblock : i * q + 1 + (q - 1) = (i + 1) * q := by rw [Nat.add_mul]; omega
  have hV' : i * q + 1 + (q - 1) ≤ V.length := by
    rw [hV, hblock]; exact Nat.mul_le_mul_right q hi
  have hFw' : p6 + 2 * (i : ℤ) = p6 + ((Fw.map (bitSymbol (a := a))).length : ℤ) := by
    rw [hFw]; push_cast; ring
  set f1 := decide (o1 = .lt)
  set f2 := decide (o2 = .gt)
  have hFw1 : p6 + 2 * (i : ℤ) + 1 = p6 + (((Fw ++ [f1]).map (bitSymbol (a := a))).length : ℤ) := by
    simp only [List.map_append, List.length_append, List.length_map, List.length_singleton]
    rw [List.length_map] at hFw; rw [hFw]; push_cast; ring
  -- compare with the first constant
  have s2 := hoare_place (cmpCells_hoare (q - 1) .eq V C1 f c1 (fun _ => blank) p0 p2 p5 (i * q + 1)
    hV' (by rw [hC1])) cmpV1
    (⟨fun j => if j = 0 then p1 else if j = 1 then p3 else if j = 2 then p4 else p6 + 2 * i,
      fun j => if j = 0 then Y else if j = 1 then K2 else if j = 2 then K3
        else putWord (fun _ => blank) p6 (Fw.map bitSymbol)⟩ : Tapes 4 a)
  rw [cmpV1_bank, cmpV1_bank, ← blank_eq_update,
    show p0 + ((i * q + 1 : ℕ) : ℤ) = p0 + i * q + 1 by push_cast; ring] at s2
  -- flag "smaller"
  have s3 := hoare_place (flagCell_hoare .lt (fun _ => blank) (putWord (fun _ => blank) p6 (Fw.map bitSymbol))
    p5 (p6 + 2 * i) o1) flagP
    (⟨fun j => if j = 0 then p0 + i * q + 1 + (q - 1 : ℕ) else if j = 1 then p1
        else if j = 2 then p2 + (q - 1 : ℕ) else if j = 3 then p3 else p4,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K1 else if j = 3 then K2
        else K3⟩ : Tapes 5 a)
  rw [flagP_bank, flagP_bank, update_blank_blank, hFw', Gather.putWord_snoc,
    show [bitSymbol (a := a) (decide (o1 = .lt))] = [f1].map bitSymbol from rfl,
    ← List.map_append (f := bitSymbol (a := a)), ← hFw'] at s3
  -- back to the block's second bit
  have s4 := backV_hoare (q - 1) Y K1 K2 K3 (fun _ => blank)
    (putWord (fun _ => blank) p6 ((Fw ++ [f1]).map bitSymbol)) X (p0 + i * q + 1 + (q - 1 : ℕ))
    p1 (p2 + (q - 1 : ℕ)) p3 p4 p5 (p6 + 2 * i + 1)
  rw [add_sub_cancel_right] at s4
  -- rewind the first constant
  have s5 := hoare_place (ReturnOrigin.return_hoare_at c1 p2 (C1.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hc1) oneC1
    (⟨fun j => if j = 0 then p0 + i * q + 1 else if j = 1 then p1 else if j = 2 then p3
        else if j = 3 then p4 else if j = 4 then p5 else p6 + 2 * i + 1,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K2 else if j = 3 then K3
        else if j = 4 then (fun _ => blank)
        else putWord (fun _ => blank) p6 ((Fw ++ [f1]).map bitSymbol)⟩ : Tapes 6 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s5
  rw [oneC1_bank, oneC1_bank, List.length_map, hC1] at s5
  -- compare with the second constant
  have s6 := hoare_place (cmpCells_hoare (q - 1) .eq V C2 f c2 (fun _ => blank) p0 p3 p5 (i * q + 1)
    hV' (by rw [hC2])) cmpV2
    (⟨fun j => if j = 0 then p1 else if j = 1 then p2 else if j = 2 then p4 else p6 + 2 * i + 1,
      fun j => if j = 0 then Y else if j = 1 then K1 else if j = 2 then K3
        else putWord (fun _ => blank) p6 ((Fw ++ [f1]).map bitSymbol)⟩ : Tapes 4 a)
  rw [cmpV2_bank, cmpV2_bank, ← blank_eq_update,
    show p0 + ((i * q + 1 : ℕ) : ℤ) = p0 + i * q + 1 by push_cast; ring] at s6
  -- flag "larger"
  have s7 := hoare_place (flagCell_hoare .gt (fun _ => blank)
    (putWord (fun _ => blank) p6 ((Fw ++ [f1]).map bitSymbol)) p5 (p6 + 2 * i + 1) o2) flagP
    (⟨fun j => if j = 0 then p0 + i * q + 1 + (q - 1 : ℕ) else if j = 1 then p1
        else if j = 2 then p2 else if j = 3 then p3 + (q - 1 : ℕ) else p4,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K1 else if j = 3 then K2
        else K3⟩ : Tapes 5 a)
  rw [flagP_bank, flagP_bank, update_blank_blank, hFw1, Gather.putWord_snoc,
    show [bitSymbol (a := a) (decide (o2 = .gt))] = [f2].map bitSymbol from rfl,
    ← List.map_append (f := bitSymbol (a := a)), ← hFw1] at s7
  -- rewind the second constant
  have s8 := hoare_place (ReturnOrigin.return_hoare_at c2 p3 (C2.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hc2) oneC2
    (⟨fun j => if j = 0 then p0 + i * q + 1 + (q - 1 : ℕ) else if j = 1 then p1 else if j = 2 then p2
        else if j = 3 then p4 else if j = 4 then p5 else p6 + 2 * i + 1 + 1,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K1 else if j = 3 then K3
        else if j = 4 then (fun _ => blank)
        else putWord (fun _ => blank) p6 ((Fw ++ [f1] ++ [f2]).map bitSymbol)⟩ : Tapes 6 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s8
  rw [oneC2_bank, oneC2_bank, List.length_map, hC2] at s8
  have hall := ((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8
  refine hall.consequence (fun v hv => by rw [hv]; rfl) (fun v hv => ?_) (by unfold digitVCost; omega)
  rw [hv, stateV, flagWordV, flagsV]
  have hhead : p0 + (i : ℤ) * q + 1 + ((q - 1 : ℕ) : ℤ) = p0 + ((i + 1 : ℕ) : ℤ) * q := by
    push_cast [show 1 ≤ q from hq]; ring
  rw [hhead, show p6 + 2 * (i : ℤ) + 1 + 1 = p6 + 2 * ((i + 1 : ℕ) : ℤ) by push_cast; ring,
    List.append_assoc, List.singleton_append]

include hW hC3 hc3 in
theorem digitW_hoare (i : ℕ) (hi : i < n) :
    HoareTime (digitW b a)
      (fun v => v = stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 i)
      (fun v => v = stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 (i + 1))
      (digitWCost b) := by
  set X := putWord f p0 (V.map bitSymbol)
  set Y := putWord g p1 (W.map bitSymbol)
  set K1 := putWord c1 p2 (C1.map bitSymbol)
  set K2 := putWord c2 p3 (C2.map bitSymbol)
  set K3 := putWord c3 p4 (C3.map bitSymbol)
  set Fw := flagWordW q b n V W C1 C2 C3 i
  set o3 := orderAfter .eq W C3 (i * b) b
  set f3 := decide (o3 = .gt)
  have hFw : (Fw.map (bitSymbol (a := a))).length = 2 * n + i := by simp [Fw, flagWordW_length]
  have hFw' : p6 + 2 * (n : ℤ) + i = p6 + ((Fw.map (bitSymbol (a := a))).length : ℤ) := by
    rw [hFw]; push_cast; ring
  have hW' : i * b + b ≤ W.length := by
    rw [hW, show i * b + b = (i + 1) * b by ring]; exact Nat.mul_le_mul_right b hi
  -- compare with the third constant
  have s1 := hoare_place (cmpCells_hoare b .eq W C3 g c3 (fun _ => blank) p1 p4 p5 (i * b)
    hW' (by rw [hC3])) cmpW
    (⟨fun j => if j = 0 then p0 + n * q else if j = 1 then p2 else if j = 2 then p3 else p6 + 2 * n + i,
      fun j => if j = 0 then X else if j = 1 then K1 else if j = 2 then K2
        else putWord (fun _ => blank) p6 (Fw.map bitSymbol)⟩ : Tapes 4 a)
  rw [cmpW_bank, cmpW_bank, ← blank_eq_update, show p1 + ((i * b : ℕ) : ℤ) = p1 + i * b by push_cast; ring]
    at s1
  -- flag "larger"
  have s2 := hoare_place (flagCell_hoare .gt (fun _ => blank) (putWord (fun _ => blank) p6 (Fw.map bitSymbol))
    p5 (p6 + 2 * n + i) o3) flagP
    (⟨fun j => if j = 0 then p0 + n * q else if j = 1 then p1 + i * b + b
        else if j = 2 then p2 else if j = 3 then p3 else p4 + b,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K1 else if j = 3 then K2
        else K3⟩ : Tapes 5 a)
  rw [flagP_bank, flagP_bank, update_blank_blank, hFw', Gather.putWord_snoc,
    show [bitSymbol (a := a) (decide (o3 = .gt))] = [f3].map bitSymbol from rfl,
    ← List.map_append (f := bitSymbol (a := a)), ← hFw'] at s2
  -- rewind the third constant
  have s3 := hoare_place (ReturnOrigin.return_hoare_at c3 p4 (C3.map bitSymbol)
    (ReturnOrigin.bits_nonblank _) hc3) oneC3
    (⟨fun j => if j = 0 then p0 + n * q else if j = 1 then p1 + i * b + b else if j = 2 then p2
        else if j = 3 then p3 else if j = 4 then p5 else p6 + 2 * n + i + 1,
      fun j => if j = 0 then X else if j = 1 then Y else if j = 2 then K1 else if j = 3 then K2
        else if j = 4 then (fun _ => blank)
        else putWord (fun _ => blank) p6 ((Fw ++ [f3]).map bitSymbol)⟩ : Tapes 6 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s3
  rw [oneC3_bank, oneC3_bank, List.length_map, hC3] at s3
  have hall := (s1.seq s2).seq s3
  refine hall.consequence (fun v hv => by rw [hv]; rfl) (fun v hv => ?_) (by unfold digitWCost; omega)
  rw [hv, stateW, flagWordW, flagsW]
  rw [show p1 + (i : ℤ) * b + b = p1 + ((i + 1 : ℕ) : ℤ) * b by push_cast; ring,
    show p6 + 2 * (n : ℤ) + i + 1 = p6 + 2 * n + ((i + 1 : ℕ) : ℤ) by push_cast; ring]

theorem stateV_zero :
    stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 0 =
      bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol))
        (putWord c1 p2 (C1.map bitSymbol)) (putWord c2 p3 (C2.map bitSymbol))
        (putWord c3 p4 (C3.map bitSymbol)) (fun _ => blank) (fun _ => blank) p0 p1 p2 p3 p4 p5 p6 := by
  simp [stateV, flagWordV, putWord]

theorem stateW_final :
    stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 n =
      bank (putWord f p0 (V.map bitSymbol)) (putWord g p1 (W.map bitSymbol))
        (putWord c1 p2 (C1.map bitSymbol)) (putWord c2 p3 (C2.map bitSymbol))
        (putWord c3 p4 (C3.map bitSymbol)) (fun _ => blank)
        (putWord (fun _ => blank) p6 ((flagWordW q b n V W C1 C2 C3 n).map bitSymbol))
        (p0 + n * q) (p1 + n * b) p2 p3 p4 p5 (p6 + 3 * n) := by
  simp only [stateW]
  congr 1
  ring

/-- The total cost. -/
def cost (q b n : ℕ) : ℕ := n * (digitVCost q + 1) + 1 + n * (digitWCost b + 1)

include hV hW hq hC1 hC2 hC3 hc1 hc2 hc3 in
/-- The guard test's contract: the words and constants are preserved, the
flag word holds every block's flags, the first word's head is past its blocks
and the second word's head past its blocks. -/
theorem program_hoare :
    HoareTime (program q b n a)
      (fun v => v = stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 0)
      (fun v => v = stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 n)
      (cost q b n) := by
  have hv := iterate_hoare (digitV q a) n (stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6)
    (digitVCost q) (fun i hi => digitV_hoare q n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 hV hq
      hC1 hC2 hc1 hc2 i hi)
  have hw := iterate_hoare (digitW b a) n (stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6)
    (digitWCost b) (fun i hi => digitW_hoare q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 hW
      hC3 hc3 i hi)
  have hmid : stateV q V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 n =
      stateW q b n V W C1 C2 C3 f g c1 c2 c3 p0 p1 p2 p3 p4 p5 p6 0 := by
    simp [stateV, stateW, flagWordW]
  rw [hmid] at hv
  exact hv.seq hw

end Machine

end IntegerMultBounds.Machine.GuardGadget

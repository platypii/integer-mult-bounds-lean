import IntegerMultBounds.Machine.Registers
import IntegerMultBounds.Machine.BinaryAccumulate
import IntegerMultBounds.Machine.BinaryDecrease
import IntegerMultBounds.Machine.BinaryMultiply
import IntegerMultBounds.Machine.BinaryDivide
import IntegerMultBounds.Machine.BinaryCompare
import IntegerMultBounds.Machine.RulerAdvance

/-! Arithmetic on natural-number registers: each macro runs a binary
arithmetic machine on canonical register words, returns the heads to the
origins and trims the result, so registers stay canonical and contracts are
stated by values only. -/

namespace IntegerMultBounds.Machine

open Registers (canon canon_value)

namespace RegAdd

variable {a : ℕ}

def bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩

def E0_1 : Fin (2 + 0) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0_1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a)).reindex E0 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 1 else 0
  invFun := fun i => if i = 0 then 1 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a)).reindex E1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (BinaryAccumulate.program a) 0) E0_1
def p2 := reindex (extend (ReturnOrigin.program (a := a)) 1) E0
def p3 := reindex (extend (ReturnOrigin.program (a := a)) 1) E1
def p4 := reindex (extend (Registers.Trim.program (a := a)) 1) E1
def program := (seq (seq (seq (p1 (a := a)) p2) p3) p4)

theorem add_hoare (x y : ℕ) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (x + y)).map bitSymbol)) (0) (0)) c ∧ c ≤ 5 * ((canon x).length + (canon y).length) + 25 := by
  have a1 := hoare_place (BinaryAccumulate.accumulate_hoare (canon x) (canon y) (fun _ => blank) (fun _ => blank) 0 0 rfl (fun _ _ _ => rfl)) E0_1
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [BinaryAccumulate.cfg, Config.tapes] at a1
  rw [E0_1_bank, E0_1_bank] at a1
  have a2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => 0 + ↑(BinaryAccumulate.sumWord (canon x) (canon y)).length, fun z => putWord (fun _ => blank) 0 ((BinaryAccumulate.sumWord (canon x) (canon y)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at a2
  rw [E0_bank, E0_bank, List.length_map] at a2
  have a3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((BinaryAccumulate.sumWord (canon x) (canon y)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E1
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at a3
  rw [E1_bank, E1_bank, List.length_map] at a3
  have a4 := hoare_place (Registers.norm_hoare (BinaryAccumulate.sumWord (canon x) (canon y))) E1
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [Registers.one] at a4
  rw [E1_bank, E1_bank, BinaryAccumulate.sumWord_value, canon_value, canon_value, Registers.reg] at a4
  have hall := (((a1.seq a2).seq a3).seq a4)
  refine ⟨_, hall, ?_⟩
  have := BinaryAccumulate.sumWord_length_le (canon x) (canon y)
  simp only [BinaryAccumulate.width, List.length_map] at *
  omega

end RegAdd

namespace RegSub

variable {a : ℕ}

def bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩

def E0_1 : Fin (2 + 0) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0_1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a)).reindex E0 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 1 else 0
  invFun := fun i => if i = 0 then 1 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a)).reindex E1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (BinaryDecrease.program a) 0) E0_1
def p2 := reindex (extend (ReturnOrigin.program (a := a)) 1) E0
def p3 := reindex (extend (ReturnOrigin.program (a := a)) 1) E1
def p4 := reindex (extend (Registers.Trim.program (a := a)) 1) E1
def program := (seq (seq (seq (p1 (a := a)) p2) p3) p4)

theorem sub_hoare (x y : ℕ) (hxy : x ≤ y) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y - x)).map bitSymbol)) (0) (0)) c ∧ c ≤ 5 * ((canon x).length + (canon y).length) + 25 := by
  have s1 := hoare_place (BinaryDecrease.decrease_hoare (canon x) (canon y) (fun _ => blank) (fun _ => blank) 0 0 rfl (fun _ _ _ => rfl)) E0_1
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [BinaryDecrease.cfg, Config.tapes] at s1
  rw [E0_1_bank, E0_1_bank, ← BinaryDecrease.diffWord_length] at s1
  have s2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => 0 + ↑(BinaryDecrease.diffWord (canon x) (canon y)).length, fun z => putWord (fun _ => blank) 0 ((BinaryDecrease.diffWord (canon x) (canon y)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s2
  rw [E0_bank, E0_bank, List.length_map] at s2
  have s3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((BinaryDecrease.diffWord (canon x) (canon y)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E1
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s3
  rw [E1_bank, E1_bank, List.length_map] at s3
  have s4 := hoare_place (Registers.norm_hoare (BinaryDecrease.diffWord (canon x) (canon y))) E1
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [Registers.one] at s4
  rw [E1_bank, E1_bank, BinaryDecrease.diffWord_value _ _ (by rw [canon_value, canon_value]; exact hxy), canon_value, canon_value, Registers.reg] at s4
  have hall := (((s1.seq s2).seq s3).seq s4)
  refine ⟨_, hall, ?_⟩
  have := BinaryDecrease.diffWord_length (canon x) (canon y)
  simp only [BinaryCompare.width, List.length_map] at *
  omega

end RegSub

namespace RegCopy

variable {a : ℕ}

def bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) : Tapes 2 a :=
  ⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩

def E0_1 : Fin (2 + 0) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0_1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 0 else 1
  invFun := fun i => if i = 0 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a)).reindex E0 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 1) ≃ Fin 2 where
  toFun := fun i => if i = 0 then 1 else 0
  invFun := fun i => if i = 0 then 1 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 : ℤ → Fin (a + 4)) (p0 p1 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a)).reindex E1 = bank f0 f1 p0 p1 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (CopyWord.program (a := a)) 0) E0_1
def p2 := reindex (extend (ReturnOrigin.program (a := a)) 1) E0
def p3 := reindex (extend (ReturnOrigin.program (a := a)) 1) E1
def program := (seq (seq (p1 (a := a)) p2) p3)

theorem copy_hoare (x : ℕ) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) ((fun _ => blank)) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (0) (0)) c ∧ c ≤ 3 * (canon x).length + 6 := by
  have c1 := hoare_place (CopyWord.copy_hoare (fun _ => blank) (fun _ => blank) 0 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0_1
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [CopyWord.cfg, Config.tapes] at c1
  rw [E0_1_bank, E0_1_bank, List.length_map] at c1
  have c2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => 0 + ↑(canon x).length, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c2
  rw [E0_bank, E0_bank, List.length_map] at c2
  have c3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E1
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c3
  rw [E1_bank, E1_bank, List.length_map] at c3
  have hall := ((c1.seq c2).seq c3)
  refine ⟨_, hall, ?_⟩
  simp only [List.length_map] at *
  omega

end RegCopy

namespace RegClear

variable {a : ℕ}

def bank (f0 : ℤ → Fin (a + 4)) (p0 : ℤ) : Tapes 1 a :=
  ⟨fun i => p0, fun i => f0⟩

def E0 : Fin (1 + 0) ≃ Fin 1 where
  toFun := fun i => 0
  invFun := fun i => 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 : ℤ → Fin (a + 4)) (p0 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0 = bank f0 p0 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (ScanEnd.program (a := a)) 0) E0
def p2 := reindex (extend (EraseBack.program (a := a)) 0) E0
def program := (seq (p1 (a := a)) p2)

theorem clear_hoare (x : ℕ) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (0)) (fun v => v = bank ((fun _ => blank)) (0)) c ∧ c ≤ 2 * (canon x).length + 3 := by
  have e1 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [ScanEnd.cfg, Config.tapes] at e1
  rw [E0_bank, E0_bank] at e1
  have e2 := hoare_place (EraseBack.erase_hoare (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E0
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [EraseBack.cfg, Config.tapes] at e2
  rw [E0_bank, E0_bank] at e2
  have hall := (e1.seq e2)
  refine ⟨_, hall, ?_⟩
  simp only [List.length_map] at *
  omega

end RegClear

namespace RegMul

variable {a : ℕ}

def bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) : Tapes 3 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p2, fun i => if i = 0 then f0 else if i = 1 then f1 else f2⟩

def E1_2 : Fin (2 + 1) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_2_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun i => if i = 0 then p1 else p2, fun i => if i = 0 then f1 else f2⟩ : Tapes 2 a).append (⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a)).reindex E1_2 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E1_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else p2, fun i => if i = 0 then f0 else f2⟩ : Tapes 2 a)).reindex E1 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0_1_2 : Fin (3 + 0) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_2_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((BinaryMultiply.bank f0 f1 f2 p0 p1 p2).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1_2 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append BinaryMultiply.bank bank E0_1_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else 1
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a)).reindex E2 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (RulerAdvance.program (a := a)) 1) E1_2
def p2 := reindex (extend (StepLeft.program (a := a)) 2) E1
def p3 := reindex (extend (BinaryMultiply.program a) 0) E0_1_2
def p4 := reindex (extend (StepRight.program (a := a)) 2) E1
def p5 := reindex (extend (Registers.Trim.program (a := a)) 2) E2
def program := (seq (seq (seq (seq (p1 (a := a)) p2) p3) p4) p5)

theorem mul_hoare (x y : ℕ) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) ((fun _ => blank)) (0) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (x * y)).map bitSymbol)) (0) (0) (0)) c ∧ c ≤ (canon y).length * (5 * (canon x).length + 2 * (canon y).length + 18) + 3 * ((canon x).length + (canon y).length) + 20 := by
  have m1 := hoare_place (RulerAdvance.advance_hoare (fun _ => blank) (fun _ => blank) 0 0 ((canon y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E1_2
    (⟨fun z => 0, fun z => putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)⟩ : Tapes 1 a)
  simp only [RulerAdvance.cfg, Config.tapes] at m1
  rw [E1_2_bank, E1_2_bank, List.length_map] at m1
  have m2 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (0 + ↑(canon y).length)) E1
    (⟨fun z => if z = 0 then 0 else 0 + ↑(canon y).length, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else (fun _ => blank)⟩ : Tapes 2 a)
  simp only [StepLeft.cfg, Config.tapes] at m2
  rw [E1_bank, E1_bank] at m2
  have m3 := hoare_place (BinaryMultiply.multiply_hoare (canon x) (canon y) (fun _ => blank) (fun _ => blank) 0 0 (0 + ↑(canon y).length) rfl rfl rfl) E0_1_2
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  rw [E0_1_2_bank, E0_1_2_bank, add_sub_cancel_right] at m3
  have m4 := hoare_place (StepRight.step_hoare (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (0 - 1)) E1
    (⟨fun z => if z = 0 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else putWord (fun _ => blank) 0 ((BinaryMultiply.horner (canon x) (canon y)).map bitSymbol)⟩ : Tapes 2 a)
  simp only [StepRight.cfg, Config.tapes] at m4
  rw [E1_bank, E1_bank, sub_add_cancel] at m4
  have m5 := hoare_place (Registers.norm_hoare (BinaryMultiply.horner (canon x) (canon y))) E2
    (⟨fun z => if z = 0 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)⟩ : Tapes 2 a)
  simp only [Registers.one] at m5
  rw [E2_bank, E2_bank, BinaryMultiply.horner_value, canon_value, canon_value, Registers.reg] at m5
  have hall := ((((m1.seq m2).seq m3).seq m4).seq m5)
  refine ⟨_, hall, ?_⟩
  have := BinaryMultiply.cost_le (canon x) (canon y)
  have := BinaryMultiply.horner_length (canon x) (canon y)
  simp only [List.length_map] at *
  omega

end RegMul

namespace RegDiv

variable {a : ℕ}

def bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) : Tapes 5 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else f4⟩

def E0_2 : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p2, fun i => if i = 0 then f0 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p3 else p4, fun i => if i = 0 then f1 else if i = 1 then f3 else f4⟩ : Tapes 3 a)).reindex E0_2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E0_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else p4, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex E0 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0_4 : Fin (2 + 3) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 4 else if i = 2 then 1 else if i = 3 then 2 else 3
  invFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_4_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p4, fun i => if i = 0 then f0 else f4⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else p3, fun i => if i = 0 then f1 else if i = 1 then f2 else f3⟩ : Tapes 3 a)).reindex E0_4 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E0_4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0_1_2_3_4 : Fin (5 + 0) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_2_3_4_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((BinaryDivide.bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1_2_3_4 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append BinaryDivide.bank bank E0_1_2_3_4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E4 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else 3
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p4, fun _ => f4⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else p3, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else f3⟩ : Tapes 4 a)).reindex E4 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 4) ≃ Fin 5 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else 4
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 f3 f4 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else f4⟩ : Tapes 4 a)).reindex E2 = bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4 := by
  unfold Tapes.reindex Tapes.append  bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (RulerAdvance.program (a := a)) 3) E0_2
def p2 := reindex (extend (ReturnOrigin.program (a := a)) 4) E0
def p3 := reindex (extend (RulerAdvance.program (a := a)) 3) E0_4
def p4 := reindex (extend (StepLeft.program (a := a)) 4) E0
def p5 := reindex (extend (BinaryDivide.program a) 0) E0_1_2_3_4
def p6 := reindex (extend (StepRight.program (a := a)) 4) E0
def p7 := reindex (extend (Registers.Trim.program (a := a)) 4) E4
def p8 := reindex (extend (Registers.Trim.program (a := a)) 4) E2
def program := (seq (seq (seq (seq (seq (seq (seq (p1 (a := a)) p2) p3) p4) p5) p6) p7) p8)

theorem div_hoare (x y : ℕ) (hy : 0 < y) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (0) (0) (0) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (x % y)).map bitSymbol)) ((fun _ => blank)) (putWord (fun _ => blank) 0 ((canon (x / y)).map bitSymbol)) (0) (0) (0) (0) (0)) c ∧ c ≤ (canon x).length * (4 * (canon x).length + 6 * (canon y).length + 27) + 8 * (canon x).length + 2 * (canon y).length + 40 := by
  have d1 := hoare_place (RulerAdvance.advance_hoare (fun _ => blank) (fun _ => blank) 0 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0_2
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 1 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 3 a)
  simp only [RulerAdvance.cfg, Config.tapes] at d1
  rw [E0_2_bank, E0_2_bank, List.length_map] at d1
  have d2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 + ↑(canon x).length else if z = 2 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 1 then (fun _ => blank) else if z = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at d2
  rw [E0_bank, E0_bank, List.length_map] at d2
  have d3 := hoare_place (RulerAdvance.advance_hoare (fun _ => blank) (fun _ => blank) 0 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0_4
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 + ↑(canon x).length else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 1 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 3 a)
  simp only [RulerAdvance.cfg, Config.tapes] at d3
  rw [E0_4_bank, E0_4_bank, List.length_map] at d3
  have d4 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (0 + ↑(canon x).length)) E0
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 + ↑(canon x).length else if z = 2 then 0 else 0 + ↑(canon x).length, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 1 then (fun _ => blank) else if z = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [StepLeft.cfg, Config.tapes] at d4
  rw [E0_bank, E0_bank] at d4
  have d5 := hoare_place (BinaryDivide.divide_hoare (canon x) (canon y) (fun _ => blank) (fun _ => blank) 0 0 (0 + ↑(canon x).length) 0 (0 + ↑(canon x).length) rfl rfl rfl) E0_1_2_3_4
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  rw [E0_1_2_3_4_bank, E0_1_2_3_4_bank, add_sub_cancel_right] at d5
  have d6 := hoare_place (StepRight.step_hoare (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (0 - 1)) E0
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 else if z = 2 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 1 then putWord (fun _ => blank) 0 ((BinaryDivide.remainder (canon y) (canon x)).map bitSymbol) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) 0 ((BinaryDivide.quotient (canon y) (canon x)).map bitSymbol)⟩ : Tapes 4 a)
  simp only [StepRight.cfg, Config.tapes] at d6
  rw [E0_bank, E0_bank, sub_add_cancel] at d6
  have d7 := hoare_place (Registers.norm_hoare (BinaryDivide.quotient (canon y) (canon x))) E4
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 else if z = 2 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else if z = 1 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 2 then putWord (fun _ => blank) 0 ((BinaryDivide.remainder (canon y) (canon x)).map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  simp only [Registers.one] at d7
  rw [E4_bank, E4_bank, (BinaryDivide.div_correct (canon y) (canon x) (by rw [canon_value]; exact hy)).2, canon_value, canon_value, Registers.reg] at d7
  have d8 := hoare_place (Registers.norm_hoare (BinaryDivide.remainder (canon y) (canon x))) E2
    (⟨fun z => if z = 0 then 0 else if z = 1 then 0 else if z = 2 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else if z = 1 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else if z = 2 then (fun _ => blank) else putWord (fun _ => blank) 0 ((canon (x / y)).map bitSymbol)⟩ : Tapes 4 a)
  simp only [Registers.one] at d8
  rw [E2_bank, E2_bank, (BinaryDivide.div_correct (canon y) (canon x) (by rw [canon_value]; exact hy)).1, canon_value, canon_value, Registers.reg] at d8
  have hall := (((((((d1.seq d2).seq d3).seq d4).seq d5).seq d6).seq d7).seq d8)
  refine ⟨_, hall, ?_⟩
  have := BinaryDivide.cost_le (canon x) (canon y)
  have := BinaryDivide.quotient_length (canon y) (canon x)
  have := BinaryDivide.remainder_length (canon y) (canon x)
  simp only [List.length_map] at *
  omega

end RegDiv

namespace RegCmp

variable {a : ℕ}

def bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) : Tapes 3 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p2, fun i => if i = 0 then f0 else if i = 1 then f1 else f2⟩

def E0_1_2 : Fin (3 + 0) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_1_2_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else if i = 1 then p1 else p2, fun i => if i = 0 then f0 else if i = 1 then f1 else f2⟩ : Tapes 3 a).append (⟨fun _ => 0, fun _ => 0⟩ : Tapes 0 a)).reindex E0_1_2 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E0_1_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else p2, fun i => if i = 0 then f1 else f2⟩ : Tapes 2 a)).reindex E0 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else p2, fun i => if i = 0 then f0 else f2⟩ : Tapes 2 a)).reindex E1 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else 1
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 : ℤ → Fin (a + 4)) (p0 p1 p2 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else p1, fun i => if i = 0 then f0 else f1⟩ : Tapes 2 a)).reindex E2 = bank f0 f1 f2 p0 p1 p2 := by
  unfold Tapes.reindex Tapes.append  bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl


def p1 := reindex (extend (BinaryCompare.program a) 0) E0_1_2
def p2 := reindex (extend (ReturnOrigin.program (a := a)) 2) E0
def p3 := reindex (extend (ReturnOrigin.program (a := a)) 2) E1
def p4 := reindex (extend (StepLeft.program (a := a)) 2) E2
def program := (seq (seq (seq (p1 (a := a)) p2) p3) p4)

theorem cmp_hoare (x y : ℕ) :
    ∃ c, HoareTime (program (a := a)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) ((fun _ => blank)) (0) (0) (0)) (fun v => v = bank (putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol)) (putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)) (putWord (fun _ => blank) 0 [bitSymbol (decide (x < y))]) (0) (0) (0)) c ∧ c ≤ 2 * ((canon x).length + (canon y).length) + 12 := by
  have q1 := hoare_place (BinaryCompare.compare_hoare (canon x) (canon y) (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 rfl rfl) E0_1_2
    (⟨fun z => 0, fun z => 0⟩ : Tapes 0 a)
  simp only [BinaryCompare.cfg, Config.tapes] at q1
  rw [E0_1_2_bank, E0_1_2_bank, BinaryCompare.resultWord, canon_value, canon_value] at q1
  have q2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E0
    (⟨fun z => if z = 0 then 0 + ↑(canon y).length else 0 + 1, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol) else putWord (fun _ => blank) 0 [bitSymbol (decide (x < y))]⟩ : Tapes 2 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at q2
  rw [E0_bank, E0_bank, List.length_map] at q2
  have q3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) 0 ((canon y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E1
    (⟨fun z => if z = 0 then 0 else 0 + 1, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else putWord (fun _ => blank) 0 [bitSymbol (decide (x < y))]⟩ : Tapes 2 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at q3
  rw [E1_bank, E1_bank, List.length_map] at q3
  have q4 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) 0 [bitSymbol (decide (x < y))]) (0 + 1)) E2
    (⟨fun z => if z = 0 then 0 else 0, fun z => if z = 0 then putWord (fun _ => blank) 0 ((canon (x)).map bitSymbol) else putWord (fun _ => blank) 0 ((canon (y)).map bitSymbol)⟩ : Tapes 2 a)
  simp only [StepLeft.cfg, Config.tapes] at q4
  rw [E2_bank, E2_bank, add_sub_cancel_right] at q4
  have hall := (((q1.seq q2).seq q3).seq q4)
  refine ⟨_, hall, ?_⟩
  simp only [BinaryCompare.width, List.length_map] at *
  omega

end RegCmp

end IntegerMultBounds.Machine

import IntegerMultBounds.Machine.BinaryAccumulate
import IntegerMultBounds.Machine.ExactFrame
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.LoopChain

/-! Literal binary multiplication by Horner's rule on three tapes. The
multiplier is read from its most significant bit downwards; each bit doubles
the accumulator by writing a zero one cell to the left of its origin, then,
when the bit is set, adds the multiplicand in place and rewinds both heads.
The accumulator's origin moves left one cell per multiplier bit, so no word
is ever copied. The multiplicand and multiplier are preserved; the cost is
quadratic in the widths, at most `m (5w + 2m + 18)` for a `w`-bit
multiplicand and `m`-bit multiplier. -/

namespace IntegerMultBounds.Machine.BinaryMultiply

variable {a : ℕ}

open BinaryAccumulate (sumWord sumWord_value sumWord_length sumWord_length_le width)

section Lists

theorem value_append (xs ys : List Bool) :
    Counter.value (xs ++ ys) = Counter.value xs + 2 ^ xs.length * Counter.value ys := by
  induction xs with
  | nil => simp [Counter.value]
  | cons x xs ih => simp [Counter.value, ih, pow_succ]; ring

/-- Without overflow the sum has exactly the common width. -/
theorem sumWord_length_eq (xs acc : List Bool)
    (h : Counter.value xs + Counter.value acc < 2 ^ width xs acc) :
    (sumWord xs acc).length = width xs acc := by
  rw [sumWord_length]
  cases hov : BinaryAdd.overflow false (BinaryAccumulate.pairs xs acc)
  · simp [BinaryAdd.carryWord]
  · exfalso
    have hv := sumWord_value xs acc
    have hlen := sumWord_length xs acc
    rw [hov] at hlen
    simp only [BinaryAdd.carryWord, ↓reduceIte, List.length_singleton] at hlen
    have hsplit : sumWord xs acc = BinaryAdd.digits false (BinaryAccumulate.pairs xs acc) ++ [true] := by
      simp [sumWord, BinaryAdd.result, hov, BinaryAdd.carryWord]
    have hd : (BinaryAdd.digits false (BinaryAccumulate.pairs xs acc)).length = width xs acc := by
      rw [BinaryAdd.digits_length, BinaryAccumulate.pairs, List.length_zip,
        BinaryAccumulate.padded_left_length, BinaryAccumulate.padded_right_length, min_self]
    rw [hsplit, value_append, hd] at hv
    simp [Counter.value] at hv
    omega

/-- Horner accumulation over the multiplier's bits, least significant bit
outermost: the bits are consumed from the most significant one down. -/
def horner (xs : List Bool) : List Bool → List Bool
  | [] => []
  | b :: rest => if b then sumWord xs (false :: horner xs rest) else false :: horner xs rest

theorem horner_value (xs ys : List Bool) :
    Counter.value (horner xs ys) = Counter.value xs * Counter.value ys := by
  induction ys with
  | nil => simp [horner, Counter.value]
  | cons b rest ih =>
    cases b <;> simp [horner, Counter.value, sumWord_value, ih] <;> ring

theorem horner_length (xs ys : List Bool) : (horner xs ys).length ≤ xs.length + ys.length := by
  induction ys with
  | nil => simp [horner]
  | cons b rest ih =>
    have ht : (false :: horner xs rest).length ≤ xs.length + (b :: rest).length := by
      simp only [List.length_cons]; omega
    cases b
    · simpa [horner] using ht
    · simp only [horner, ↓reduceIte]
      by_cases hw : width xs (false :: horner xs rest) < xs.length + (true :: rest).length
      · have := sumWord_length_le xs (false :: horner xs rest)
        omega
      · have hwe : width xs (false :: horner xs rest) = xs.length + (true :: rest).length := by
          have : width xs (false :: horner xs rest) ≤ xs.length + (true :: rest).length := by
            simp only [width, List.length_cons] at ht ⊢
            omega
          omega
        have hv : Counter.value (sumWord xs (false :: horner xs rest)) =
            Counter.value xs * Counter.value (true :: rest) := by
          have := horner_value xs (true :: rest)
          simpa [horner] using this
        rw [sumWord_length_eq xs _ (by
          rw [hwe, ← sumWord_value, hv, pow_add]
          exact mul_lt_mul'' (Counter.value_lt xs) (Counter.value_lt (true :: rest))
            (Nat.zero_le _) (Nat.zero_le _)), hwe]

theorem putWord_getElem (f : ℤ → Fin (a + 4)) (p : ℤ) (xs : List (Fin (a + 4))) (k : ℕ)
    (hk : k < xs.length) : putWord f p xs (p + k) = xs[k] := by
  induction xs generalizing f p k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [putWord_head]
    | succ k =>
      rw [putWord_cons, show p + ((k + 1 : ℕ) : ℤ) = p + 1 + k by omega,
        ih _ (p + 1) k (by simpa using hk)]
      rfl

end Lists

section Machine

/-- The three-tape bank: multiplicand, multiplier, accumulator. -/
def bank (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) : Tapes 3 a :=
  ⟨fun i => if i = 0 then px else if i = 1 then py else pacc,
   fun i => if i = 0 then f else if i = 1 then g else h⟩

/-- The accumulator's two tapes at slots zero and two. -/
def accPlace : Fin (2 + 1) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else 1
  invFun := fun i => if i = 0 then 0 else if i = 1 then 2 else 1
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at slot two. -/
def accOnly : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else 1
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- A one-tape routine at slot one. -/
def yOnly : Fin (1 + 2) ≃ Fin 3 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def accumulatePart (a : ℕ) : Program 3 3 a := reindex (extend (BinaryAccumulate.program a) 1) accPlace
def returnX (a : ℕ) : Program 3 3 a := extend (ReturnOrigin.program (a := a)) 2
def returnAcc (a : ℕ) : Program 3 3 a := reindex (extend (ReturnOrigin.program (a := a)) 2) accOnly
def prependAcc (a : ℕ) : Program 3 3 a := reindex (extend (PrependZero.program (a := a)) 2) accOnly
def stepY (a : ℕ) : Program 3 2 a := reindex (extend (StepLeft.program (a := a)) 2) yOnly

def addPart (a : ℕ) : Program 3 9 a := seq (seq (accumulatePart a) (returnX a)) (returnAcc a)

/-- Add when the scanned multiplier bit is one. -/
def cond (a : ℕ) : Program 3 11 a :=
  branch (fun s => decide (s 1 = bitSymbol true)) (addPart a) (skip 3 a (by decide))

def body (a : ℕ) : Program 3 16 a := seq (seq (prependAcc a) (cond a)) (stepY a)

def test (s : Fin 3 → Fin (a + 4)) : Bool := decide (s 1 ≠ blank)

/-- The multiplier: loop over the multiplier's bits while its head reads one. -/
def program (a : ℕ) : Program 3 17 a := whileLoop (body a) test

theorem acc_bank (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) (s : Fin 3) :
    ((BinaryAccumulate.cfg f h px pacc s).tapes.append
      (⟨fun _ => py, fun _ => g⟩ : Tapes 1 a)).reindex accPlace = bank f g h px py pacc := by
  unfold Tapes.reindex Tapes.append BinaryAccumulate.cfg Config.tapes bank accPlace
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem x_bank (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) :
    (⟨fun _ => px, fun _ => f⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then py else pacc, fun i => if i = 0 then g else h⟩ : Tapes 2 a) =
      bank f g h px py pacc := by
  unfold Tapes.append bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem acc_only_bank (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) :
    ((⟨fun _ => pacc, fun _ => h⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then px else py, fun i => if i = 0 then f else g⟩ : Tapes 2 a)).reindex
        accOnly = bank f g h px py pacc := by
  unfold Tapes.reindex Tapes.append bank accOnly
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem y_bank (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) :
    ((⟨fun _ => py, fun _ => g⟩ : Tapes 1 a).append
      (⟨fun i => if i = 0 then px else pacc, fun i => if i = 0 then f else h⟩ : Tapes 2 a)).reindex
        yOnly = bank f g h px py pacc := by
  unfold Tapes.reindex Tapes.append bank yOnly
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem bank_reads (f g h : ℤ → Fin (a + 4)) (px py pacc : ℤ) :
    (bank f g h px py pacc).reads 1 = g py := by
  simp [Tapes.reads, bank]

variable (xs ys : List Bool) (f g : ℤ → Fin (a + 4)) (px py pacc : ℤ)

/-- The bank after the top `i` multiplier bits have been consumed. -/
def state (i : ℕ) : Tapes 3 a :=
  bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
    (putWord (fun _ => blank) (pacc - i) ((horner xs (ys.drop (ys.length - i))).map bitSymbol))
    px (py + ys.length - i - 1) (pacc - i)

/-- The bank after the doubling step of iteration `i`. -/
def doubled (i : ℕ) : Tapes 3 a :=
  bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
    (putWord (fun _ => blank) (pacc - i - 1)
      ((false :: horner xs (ys.drop (ys.length - i))).map bitSymbol))
    px (py + ys.length - i - 1) (pacc - i - 1)

theorem prepend_step (i : ℕ) :
    HoareTime (prependAcc a) (fun v => v = state xs ys f g px py pacc i)
      (fun v => v = doubled xs ys f g px py pacc i) 2 := by
  have h := hoare_place (PrependZero.prepend_hoare (a := a)
    (putWord (fun _ => blank) (pacc - i) ((horner xs (ys.drop (ys.length - i))).map bitSymbol))
    (pacc - i)) accOnly
    (⟨fun j => if j = 0 then px else py + ys.length - i - 1,
      fun j => if j = 0 then putWord f px (xs.map bitSymbol) else putWord g py (ys.map bitSymbol)⟩ :
      Tapes 2 a)
  simp only [PrependZero.cfg, Config.tapes] at h
  rw [acc_only_bank, acc_only_bank, PrependZero.putWord_prepend] at h
  exact h

/-- The current multiplier bit of iteration `i`. -/
def bit (i : ℕ) (hi : i < ys.length) : Bool := ys[ys.length - i - 1]

theorem drop_succ (i : ℕ) (hi : i < ys.length) :
    ys.drop (ys.length - (i + 1)) = bit ys i hi :: ys.drop (ys.length - i) := by
  rw [List.drop_eq_getElem_cons (by omega)]
  congr 2
  omega

theorem doubled_reads (i : ℕ) (hi : i < ys.length) :
    (doubled xs ys f g px py pacc i).reads 1 = bitSymbol (bit ys i hi) := by
  rw [doubled, bank_reads, show py + (ys.length : ℤ) - i - 1 = py + ((ys.length - i - 1 : ℕ) : ℤ) by
    omega]
  rw [putWord_getElem _ _ _ _ (by simp; omega)]
  simp [bit]

theorem state_reads (i : ℕ) (hi : i < ys.length) :
    (state xs ys f g px py pacc i).reads 1 = bitSymbol (bit ys i hi) := by
  rw [state, bank_reads, show py + (ys.length : ℤ) - i - 1 = py + ((ys.length - i - 1 : ℕ) : ℤ) by
    omega]
  rw [putWord_getElem _ _ _ _ (by simp; omega)]
  simp [bit]

theorem state_exit_reads (hyl : g (py - 1) = blank) :
    (state xs ys f g px py pacc ys.length).reads 1 = blank := by
  rw [state, bank_reads, putWord_outside _ _ _ _ (Or.inl (by omega)),
    show py + (ys.length : ℤ) - ys.length - 1 = py - 1 by ring]
  exact hyl

/-- The bank after the conditional addition of iteration `i`. -/
def added (i : ℕ) : Tapes 3 a :=
  bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
    (putWord (fun _ => blank) (pacc - i - 1)
      ((horner xs (ys.drop (ys.length - (i + 1)))).map bitSymbol))
    px (py + ys.length - i - 1) (pacc - i - 1)

/-- The cost of the addition branch at iteration `i`. -/
def addCost (i : ℕ) : ℕ :=
  (width xs (false :: horner xs (ys.drop (ys.length - i))) + 1) + 1 + (xs.length + 2) + 1 +
    ((sumWord xs (false :: horner xs (ys.drop (ys.length - i)))).length + 2)

theorem add_step (hxl : f (px - 1) = blank) (hxr : f (px + xs.length) = blank) (i : ℕ) :
    HoareTime (addPart a) (fun v => v = doubled xs ys f g px py pacc i)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
        (putWord (fun _ => blank) (pacc - i - 1)
          ((sumWord xs (false :: horner xs (ys.drop (ys.length - i)))).map bitSymbol))
        px (py + ys.length - i - 1) (pacc - i - 1))
      (addCost xs ys i) := by
  set t := false :: horner xs (ys.drop (ys.length - i)) with ht
  have h1 := hoare_place (BinaryAccumulate.accumulate_hoare xs t f (fun _ => blank) px
    (pacc - i - 1) hxr (fun _ _ _ => rfl)) accPlace
    (⟨fun _ => py + ys.length - i - 1, fun _ => putWord g py (ys.map bitSymbol)⟩ : Tapes 1 a)
  rw [acc_bank, acc_bank] at h1
  have h2 := hoare_extend_eq (ReturnOrigin.return_hoare_at f px (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) hxl)
    (⟨fun j => if j = 0 then py + ys.length - i - 1 else pacc - i - 1 + (sumWord xs t).length,
      fun j => if j = 0 then putWord g py (ys.map bitSymbol)
        else putWord (fun _ => blank) (pacc - i - 1) ((sumWord xs t).map bitSymbol)⟩ : Tapes 2 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h2
  rw [x_bank, x_bank, List.length_map] at h2
  have h3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) (pacc - i - 1)
    ((sumWord xs t).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) accOnly
    (⟨fun j => if j = 0 then px else py + ys.length - i - 1,
      fun j => if j = 0 then putWord f px (xs.map bitSymbol) else putWord g py (ys.map bitSymbol)⟩ :
      Tapes 2 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at h3
  rw [acc_only_bank, acc_only_bank, List.length_map] at h3
  exact (h1.seq h2).seq h3

theorem cond_step (hxl : f (px - 1) = blank) (hxr : f (px + xs.length) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (cond a) (fun v => v = doubled xs ys f g px py pacc i)
      (fun v => v = added xs ys f g px py pacc i) (max (addCost xs ys i) 0 + 1) := by
  unfold cond
  have hread : decide ((doubled xs ys f g px py pacc i).reads 1 = bitSymbol true) = bit ys i hi := by
    rw [doubled_reads xs ys f g px py pacc i hi]
    cases bit ys i hi <;> simp [bitSymbol]
  cases hb : bit ys i hi
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) ((skip_hoare _ _).consequence
      (fun v hv => hv.1) (fun v hv => ?_) le_rfl)
    · exfalso; rw [hv, hread, hb] at hv'; simp at hv'
    · rw [hv, doubled, added, drop_succ ys i hi, hb, horner]; simp
  · refine branch_hoare _ ((add_step xs ys f g px py pacc hxl hxr i).consequence
      (fun v hv => hv.1) (fun v hv => ?_) le_rfl) (fun v ⟨hv, hv'⟩ => ?_)
    · rw [hv, added, drop_succ ys i hi, hb, horner]; simp
    · exfalso; rw [hv, hread, hb] at hv'; simp at hv'

theorem stepY_step (i : ℕ) :
    HoareTime (stepY a) (fun v => v = added xs ys f g px py pacc i)
      (fun v => v = state xs ys f g px py pacc (i + 1)) 1 := by
  have h := hoare_place (StepLeft.step_hoare (a := a) (putWord g py (ys.map bitSymbol))
    (py + ys.length - i - 1)) yOnly
    (⟨fun j => if j = 0 then px else pacc - i - 1,
      fun j => if j = 0 then putWord f px (xs.map bitSymbol)
        else putWord (fun _ => blank) (pacc - i - 1)
          ((horner xs (ys.drop (ys.length - (i + 1)))).map bitSymbol)⟩ : Tapes 2 a)
  simp only [StepLeft.cfg, Config.tapes] at h
  rw [y_bank, y_bank] at h
  refine h.consequence (fun v hv => hv) (fun v hv => ?_) le_rfl
  rw [hv, state]
  congr 1 <;> push_cast <;> ring_nf

/-- The exact body cost at iteration `i`. -/
def iterCost (i : ℕ) : ℕ := 2 + 1 + (max (addCost xs ys i) 0 + 1) + 1 + 1

theorem body_step (hxl : f (px - 1) = blank) (hxr : f (px + xs.length) = blank) (i : ℕ)
    (hi : i < ys.length) :
    HoareTime (body a) (fun v => v = state xs ys f g px py pacc i)
      (fun v => v = state xs ys f g px py pacc (i + 1)) (iterCost xs ys i) :=
  ((prepend_step xs ys f g px py pacc i).seq (cond_step xs ys f g px py pacc hxl hxr i hi)).seq
    (stepY_step xs ys f g px py pacc i)

/-- The complete multiplication: from the multiplier's most significant bit
to the blank before it, with the product on the accumulator. -/
theorem loop_hoare (hxl : f (px - 1) = blank) (hxr : f (px + xs.length) = blank)
    (hyl : g (py - 1) = blank) :
    HoareTime (program a) (fun v => v = state xs ys f g px py pacc 0)
      (fun v => v = state xs ys f g px py pacc ys.length)
      (∑ i ∈ Finset.range ys.length, (iterCost xs ys i + 2)) :=
  while_chain_hoare (body a) test (state xs ys f g px py pacc) (iterCost xs ys) ys.length
    (fun i hi => body_step xs ys f g px py pacc hxl hxr i hi)
    (fun i hi => by
      simp only [test, state_reads xs ys f g px py pacc i hi]
      cases bit ys i hi <;> simp [bitSymbol, blank])
    (by simp [test, state_exit_reads xs ys f g px py pacc hyl])

theorem state_zero : state xs ys f g px py pacc 0 =
    bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol)) (fun _ => blank)
      px (py + ys.length - 1) pacc := by
  simp [state, horner, putWord]

theorem state_final : state xs ys f g px py pacc ys.length =
    bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
      (putWord (fun _ => blank) (pacc - ys.length) ((horner xs ys).map bitSymbol))
      px (py - 1) (pacc - ys.length) := by
  simp [state]

/-- The multiplication contract in terms of the input words. -/
theorem multiply_hoare (hxl : f (px - 1) = blank) (hxr : f (px + xs.length) = blank)
    (hyl : g (py - 1) = blank) :
    HoareTime (program a)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
        (fun _ => blank) px (py + ys.length - 1) pacc)
      (fun v => v = bank (putWord f px (xs.map bitSymbol)) (putWord g py (ys.map bitSymbol))
        (putWord (fun _ => blank) (pacc - ys.length) ((horner xs ys).map bitSymbol))
        px (py - 1) (pacc - ys.length))
      (∑ i ∈ Finset.range ys.length, (iterCost xs ys i + 2)) := by
  have h := loop_hoare xs ys f g px py pacc hxl hxr hyl
  rw [state_zero, state_final] at h
  exact h

end Machine

section Cost

variable (xs ys : List Bool)

theorem addCost_le (i : ℕ) : addCost xs ys i ≤ 5 * xs.length + 2 * ys.length + 10 := by
  have hh := horner_length xs (ys.drop (ys.length - i))
  have hd : (ys.drop (ys.length - i)).length ≤ ys.length := by simp
  have hw : width xs (false :: horner xs (ys.drop (ys.length - i))) ≤
      2 * xs.length + ys.length + 1 := by
    simp only [width, List.length_cons]
    omega
  have hs := sumWord_length_le xs (false :: horner xs (ys.drop (ys.length - i)))
  unfold addCost
  omega

theorem iterCost_le (i : ℕ) : iterCost xs ys i + 2 ≤ 5 * xs.length + 2 * ys.length + 18 := by
  have := addCost_le xs ys i
  unfold iterCost
  omega

/-- The total cost is at most `m (5w + 2m + 18)`. -/
theorem cost_le :
    ∑ i ∈ Finset.range ys.length, (iterCost xs ys i + 2) ≤
      ys.length * (5 * xs.length + 2 * ys.length + 18) := by
  calc ∑ i ∈ Finset.range ys.length, (iterCost xs ys i + 2)
      ≤ ∑ _i ∈ Finset.range ys.length, (5 * xs.length + 2 * ys.length + 18) :=
        Finset.sum_le_sum fun i _ => iterCost_le xs ys i
    _ = ys.length * (5 * xs.length + 2 * ys.length + 18) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Cost

end IntegerMultBounds.Machine.BinaryMultiply

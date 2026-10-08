import IntegerMultBounds.Machine.RadixRationalData
import IntegerMultBounds.Machine.RadixUnary
import IntegerMultBounds.Swap.Modular

/-! Literal fixed-rational coefficient multiplication in prime-radix words.
A fixed finite signed-carry table processes each digit in one transition. -/

namespace IntegerMultBounds.Machine.RadixRational

open RadixDigits RadixRationalData
variable {q d : ℕ} {a : ℤ} [Fact q.Prime]

/-- One fixed finite lookup selects the quotient digit and next remainder carry. -/
def next : RadixUnary.Table q (2 * a.natAbs + d + 1) := fun c x => (carry c x,digit c x)

/-- The prime radix and denominator are fixed before selecting the input width. -/
def program (q : ℕ) (a : ℤ) (d : ℕ) [Fact q.Prime] : Program 2 (2 * a.natAbs + d + 1) q :=
  RadixUnary.program q _ (initial a d) next

abbrev cfg := @RadixUnary.cfg

theorem outputs_eq (c : State a d) (xs : List (Fin q)) :
    RadixUnary.outputs next c xs = digits c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.outputs,next,digits,ih]

theorem finalState_eq (c : State a d) (xs : List (Fin q)) :
    RadixUnary.finalState next c xs = overflow c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.finalState,next,overflow,ih]

/-- Every source digit costs exactly one transition; arbitrary source and output
background cells outside the written output interval are preserved. -/
theorem columns_run (c : State a d) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) :
    run (program q a d) xs.length
      (cfg (putWord source p (xs.map digitSymbol)) out p r c) =
      some (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) := by
  simpa only [program,outputs_eq,finalState_eq] using
    RadixUnary.columns_run (initial a d) c next xs source out p r

/-- Exact-width execution and actual halt at the terminating blank, with the
outgoing remainder carry retained as the final finite control state. -/
theorem rational_exact (c : State a d) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) (hf : source (p + xs.length) = blank) :
    run (program q a d) xs.length
      (cfg (putWord source p (xs.map digitSymbol)) out p r c) =
      some (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) ∧
    step (program q a d)
      (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) = none := by
  simpa only [program,outputs_eq,finalState_eq] using
    RadixUnary.exact_run (initial a d) c next xs source out p r (by rw [hf,readDigit_blank])


/-- Every denominator below the fixed prime stays invertible at every width. -/
theorem denominator_coprime (r : ℚ) (hden : r.den < q) (b : ℕ) : r.den.Coprime (q ^ b) := by
  have hh : q.Coprime r.den := by
    rw [(Fact.out : q.Prime).coprime_iff_not_dvd]
    intro hdvd
    exact absurd (Nat.le_of_dvd r.den_pos hdvd) (not_le.mpr hden)
  exact Nat.Coprime.pow_right b hh.symm

private theorem cancellation (r : ℚ) (hden : r.den < q) (b : ℕ) (x y : ZMod (q ^ b))
    (h : (r.den : ZMod (q ^ b)) * y = r.num * x) :
    y = Swap.Modular.ratMod (q ^ b) r * x := by
  apply Swap.Modular.cancel_coprime _ (denominator_coprime r hden b)
  calc
    y * r.den = r.num * x := by simpa only [mul_comm] using h
    _ = Swap.Modular.ratMod (q ^ b) r * x * r.den := by
      rw [mul_right_comm _ x,Swap.Modular.ratMod_mul_den _ (denominator_coprime r hden b)]

/-- The computed word realizes the same rational coefficient reduction used by
actual modular matrix operators, including negative numerators. -/
theorem output_ratMod (r : ℚ) (hden : r.den < q) (xs : List (Fin q)) :
    (value (digits (initial r.num r.den) xs) : ZMod (q ^ xs.length)) =
      Swap.Modular.ratMod (q ^ xs.length) r * (value xs : ZMod (q ^ xs.length)) := by
  apply cancellation r hden xs.length
  have hh := congrArg (fun z : ℤ => (z : ZMod (q ^ xs.length)))
    (initial_value (a := r.num) r.den_pos hden xs)
  have hz : (q : ZMod (q ^ xs.length)) ^ xs.length = 0 := by
    simpa only [Nat.cast_pow] using ZMod.natCast_self (q ^ xs.length)
  simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_add,Int.cast_pow,hz,zero_mul,add_zero] using hh

/-- Full literal-machine contract for one arbitrary rational coefficient. -/
theorem rational_hoare (r : ℚ) (hden : r.den < q) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p t : ℤ) (hf : source (p + xs.length) = blank) :
    HoareTime (program q r.num r.den)
      (fun v => v = (cfg (putWord source p (xs.map digitSymbol)) out p t (initial r.num r.den)).tapes)
      (fun v => ∃ result : List (Fin q),
        (value result : ZMod (q ^ xs.length)) =
          Swap.Modular.ratMod (q ^ xs.length) r * (value xs : ZMod (q ^ xs.length)) ∧
        result.length = xs.length ∧ v =
          (cfg (putWord source p (xs.map digitSymbol)) (putWord out t (result.map digitSymbol))
            (p + xs.length) (t + xs.length) (initial r.num r.den)).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := rational_exact (initial r.num r.den) xs source out p t hf
  exact ⟨_,_,le_rfl,hr,hh,digits (initial r.num r.den) xs,output_ratMod r hden xs,
    digits_length _ _,rfl⟩

/-- Complete blank-output execution, with the same ratMod coefficient used by
the modular network and exactly one charged transition per source digit. -/
theorem rational_to_blank (r : ℚ) (hden : r.den < q) (xs : List (Fin q)) :
    let result := digits (initial r.num r.den) xs
    let finalCarry := overflow (initial r.num r.den) xs
    (value result : ZMod (q ^ xs.length)) =
      Swap.Modular.ratMod (q ^ xs.length) r * (value xs : ZMod (q ^ xs.length)) ∧
    result.length = xs.length ∧
    run (program q r.num r.den) xs.length
      (cfg (wordTape (xs.map digitSymbol)) (fun _ => blank) 0 0 (initial r.num r.den)) =
      some (cfg (wordTape (xs.map digitSymbol)) (wordTape (result.map digitSymbol))
        xs.length xs.length finalCarry) ∧
    step (program q r.num r.den)
      (cfg (wordTape (xs.map digitSymbol)) (wordTape (result.map digitSymbol))
        xs.length xs.length finalCarry) = none := by
  refine ⟨output_ratMod r hden xs,digits_length _ _,?_⟩
  simpa only [program,outputs_eq,finalState_eq] using RadixUnary.to_blank (initial r.num r.den) next xs

end IntegerMultBounds.Machine.RadixRational

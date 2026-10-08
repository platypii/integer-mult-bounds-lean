import IntegerMultBounds.Machine.RadixDivisionData
import IntegerMultBounds.Machine.RadixUnary

/-! Literal division by a fixed denominator in prime-radix words. Two tapes
and d carry states suffice for every width. The finite transition table makes
one lookup and one transition per digit; the source tape is preserved. -/

namespace IntegerMultBounds.Machine.RadixDivide

open RadixDigits RadixDivisionData
variable {q d : ℕ} [Fact q.Prime]

/-- One fixed finite lookup selects the quotient digit and next remainder carry. -/
def next : RadixUnary.Table q d := fun c x => (carry c x,digit c x)

/-- The prime radix and denominator are fixed before selecting the input width. -/
def program (q d : ℕ) [Fact q.Prime] (hdpos : 0 < d) : Program 2 d q :=
  RadixUnary.program q d ⟨0,hdpos⟩ next

abbrev cfg := @RadixUnary.cfg

theorem outputs_eq (c : Fin d) (xs : List (Fin q)) :
    RadixUnary.outputs next c xs = digits c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.outputs,next,digits,ih]

theorem finalState_eq (c : Fin d) (xs : List (Fin q)) :
    RadixUnary.finalState next c xs = overflow c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.finalState,next,overflow,ih]

/-- Every source digit costs exactly one transition; arbitrary source and output
background cells outside the written output interval are preserved. -/
theorem columns_run (hdpos : 0 < d) (c : Fin d) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) :
    run (program q d hdpos) xs.length
      (cfg (putWord source p (xs.map digitSymbol)) out p r c) =
      some (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) := by
  simpa only [program,outputs_eq,finalState_eq] using
    RadixUnary.columns_run ⟨0,hdpos⟩ c next xs source out p r

/-- Exact-width execution and actual halt at the terminating blank, with the
outgoing remainder carry retained as the final finite control state. -/
theorem divide_exact (hdpos : 0 < d) (c : Fin d) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) (hf : source (p + xs.length) = blank) :
    run (program q d hdpos) xs.length
      (cfg (putWord source p (xs.map digitSymbol)) out p r c) =
      some (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) ∧
    step (program q d hdpos)
      (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) = none := by
  simpa only [program,outputs_eq,finalState_eq] using
    RadixUnary.exact_run ⟨0,hdpos⟩ c next xs source out p r (by rw [hf,readDigit_blank])

/-- The ordinary zero-carry entry computes fixed-denominator modular division
in linear time on the literal machine. -/
theorem divide_hoare (hdpos : 0 < d) (hdq : d < q) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) (hf : source (p + xs.length) = blank) :
    HoareTime (program q d hdpos)
      (fun v => v = (cfg (putWord source p (xs.map digitSymbol)) out p r ⟨0,hdpos⟩).tapes)
      (fun v => ∃ quotient : List (Fin q),
        (d * value quotient) % q ^ xs.length = value xs ∧ quotient.length = xs.length ∧
        v = (cfg (putWord source p (xs.map digitSymbol))
          (putWord out r (quotient.map digitSymbol)) (p + xs.length) (r + xs.length) ⟨0,hdpos⟩).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := divide_exact hdpos ⟨0,hdpos⟩ xs source out p r hf
  exact ⟨_,_,le_rfl,hr,hh,digits ⟨0,hdpos⟩ xs,divides_mod hdpos hdq xs,digits_length _ _,rfl⟩

/-- Blank-output specialization combines modular division, exact carry identity,
fixed width, literal runtime, halting, and complete source preservation. -/
theorem divide_to_blank (hdpos : 0 < d) (hdq : d < q) (xs : List (Fin q)) :
    let quotient := digits (⟨0,hdpos⟩ : Fin d) xs
    let finalCarry := overflow (⟨0,hdpos⟩ : Fin d) xs
    (d * value quotient) % q ^ xs.length = value xs ∧
    d * value quotient = value xs + q ^ xs.length * finalCarry.val ∧
    quotient.length = xs.length ∧
    run (program q d hdpos) xs.length
      (cfg (wordTape (xs.map digitSymbol)) (fun _ => blank) 0 0 ⟨0,hdpos⟩) =
      some (cfg (wordTape (xs.map digitSymbol)) (wordTape (quotient.map digitSymbol))
        xs.length xs.length finalCarry) ∧
    step (program q d hdpos)
      (cfg (wordTape (xs.map digitSymbol)) (wordTape (quotient.map digitSymbol))
        xs.length xs.length finalCarry) = none := by
  have hw (ds : List (Fin q)) : putWord (fun _ => (blank : Fin (q + 4))) 0 (ds.map digitSymbol) =
      wordTape (ds.map digitSymbol) := by
    funext j
    simpa using putWord_blank 0 j (ds.map digitSymbol)
  obtain ⟨hr,hh⟩ := divide_exact hdpos ⟨0,hdpos⟩ xs
    (fun _ => (blank : Fin (q + 4))) (fun _ => blank) 0 0 rfl
  refine ⟨divides_mod hdpos hdq xs,?_,digits_length _ _,?_,?_⟩
  · simpa using digits_value hdpos hdq ⟨0,hdpos⟩ xs
  · simpa only [hw,zero_add] using hr
  · simpa only [hw,zero_add] using hh

end IntegerMultBounds.Machine.RadixDivide

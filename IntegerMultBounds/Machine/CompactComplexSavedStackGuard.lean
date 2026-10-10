import IntegerMultBounds.Machine.CompactComplexSavedStackTailInvariant
import IntegerMultBounds.Machine.FiniteReturnGuard

/-! The physical empty-stack probe classifies genuine push histories. Positive
fixed frame width makes the last occupied cell a binary symbol, so the guard
is empty exactly at the original stack head. -/
namespace IntegerMultBounds.Machine.CompactComplexSavedStackGuard
open CompactComplexSavedStackTailInvariant (History)
variable {a t width : ℕ} {origin head : ℤ} {f : ℤ → Fin (a+4)}

theorem head_ge_origin (h : History width origin f head) : origin≤head := by
  induction h with
  | empty => exact le_rfl
  | push older code ih => omega

theorem below_origin (h : History width origin f head) (z : ℤ) (hz : z<origin) :
    f z=blank := by
  induction h with
  | empty => rfl
  | push older code ih =>
    have ht := head_ge_origin older
    rw [FiniteReturnStack.wordPart,dite_eq_right (by omega)]
    exact ih

/-- The actual cell read by the guard distinguishes an empty history from
an occupied one; no occupied-word equality is used to infer blank tails. -/
theorem probe_blank_iff (h : History width origin f head) (hw : 0<width) :
    f (head-1)=blank ↔ head=origin := by
  cases h with
  | empty => simp
  | @push older top hOlder code =>
    have htop := head_ge_origin hOlder
    have hcell : top≤top+(width : ℤ)-1 ∧ top+(width : ℤ)-1<top+width := by omega
    rw [FiniteReturnStack.wordPart,dite_eq_left hcell]
    have hbit : ∀ b : Bool,(bitSymbol b : Fin (a+4))≠blank := by
      intro b
      cases b <;> simp [bitSymbol,blank,Fin.ext_iff]
    constructor
    · intro he
      exact (hbit _ he).elim
    · intro he
      omega

/-- The two actual guard transitions retain the whole bank and return the
literal empty/nonempty state determined by the reached stack history. -/
theorem guard_run (slot : Fin t) (v : Tapes t a) (origin : ℤ)
    (h : History width origin (v.tape slot) (v.head slot)) (hw : 0<width) :
    run (FiniteReturnGuard.program slot) 2 (v.start (FiniteReturnGuard.program slot))=
      some (FiniteReturnGuard.terminal v (decide (v.head slot=origin))) := by
  rw [FiniteReturnGuard.exact_run]
  simp only [probe_blank_iff h hw]

theorem root_probe (slot : Fin t) (v : Tapes t a) (origin : ℤ)
    (h : History width origin (v.tape slot) (v.head slot)) (hw : 0<width)
    (hroot : v.head slot=origin) : v.tape slot (v.head slot-1)=blank :=
  (probe_blank_iff h hw).mpr hroot

theorem child_probe (slot : Fin t) (v : Tapes t a) (origin : ℤ)
    (h : History width origin (v.tape slot) (v.head slot)) (hw : 0<width)
    (hchild : origin<v.head slot) : v.tape slot (v.head slot-1)≠blank := by
  intro he
  have := (probe_blank_iff h hw).mp he
  omega

end IntegerMultBounds.Machine.CompactComplexSavedStackGuard

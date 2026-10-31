module

public import IntegerMultBounds.Machine.BinaryCompare

/-! Fixed head intervals for the actual binary comparison. Operand heads park
on their blank endpoints; the result head moves exactly once. -/
@[expose] public section
namespace IntegerMultBounds.Machine.BinaryCompare
variable {a : ℕ}

structure HeadBounds (lo₀ hi₀ lo₁ hi₁ r : ℤ) (c : Config 3 4 a) : Prop where
  left : lo₀ ≤ c.head 0 ∧ c.head 0 ≤ hi₀
  right : lo₁ ≤ c.head 1 ∧ c.head 1 ≤ hi₁
  result : r ≤ c.head 2 ∧ c.head 2 ≤ r+1
  active : c.state ≠ 3 → c.head 2 = r
  leftEnd : c.tape 0 hi₀ = blank
  rightEnd : c.tape 1 hi₁ = blank

private theorem advance_bound (z lo hi : ℤ) (s : Fin (a+4))
    (hz : lo ≤ z ∧ z ≤ hi) (hend : z = hi → s = blank) :
    lo ≤ z+(if s = blank then Move.stay else Move.right).offset ∧
      z+(if s = blank then Move.stay else Move.right).offset ≤ hi := by
  split_ifs with hs <;> simp only [Move.offset] <;> omega

/-- Every concrete comparison transition preserves the fixed intervals. -/
theorem HeadBounds.step {lo₀ hi₀ lo₁ hi₁ r : ℤ} {c c' : Config 3 4 a}
    (h : HeadBounds lo₀ hi₀ lo₁ hi₁ r c) (hs : step (program a) c = some c') :
    HeadBounds lo₀ hi₀ lo₁ hi₁ r c' := by
  have hstate : c.state ≠ 3 := by
    intro he
    simp [Machine.step,program,he] at hs
  have hleftEnd := h.leftEnd
  have hrightEnd := h.rightEnd
  have hr := h.active hstate
  have hl := advance_bound (c.head 0) lo₀ hi₀ (c.tape 0 (c.head 0)) h.left
    (by intro he; rw [he]; exact h.leftEnd)
  have hd := advance_bound (c.head 1) lo₁ hi₁ (c.tape 1 (c.head 1)) h.right
    (by intro he; rw [he]; exact h.rightEnd)
  unfold Machine.step at hs
  simp only [program,ite_eq_right hstate] at hs
  by_cases hb : c.tape 0 (c.head 0) = blank ∧ c.tape 1 (c.head 1) = blank
  · simp only [ite_eq_left hb,Option.some.injEq] at hs
    subst c'
    constructor
    · simpa [Move.offset] using h.left
    · simpa [Move.offset] using h.right
    · simp [hr,Move.offset]
    · simp
    · dsimp only
      simp only [show (0 : Fin 3) ≠ 2 by decide,ite_false]
      split <;> simp_all
    · dsimp only
      simp only [show (1 : Fin 3) ≠ 2 by decide,ite_false]
      split <;> simp_all
  · simp only [ite_eq_right hb] at hs
    by_cases hi : isInput (c.tape 0 (c.head 0)) ∧ isInput (c.tape 1 (c.head 1))
    · simp only [ite_eq_left hi,Option.some.injEq] at hs
      subst c'
      constructor
      · simpa using hl
      · simpa using hd
      · simpa [Move.offset] using h.result
      · intro _; simpa [Move.offset] using hr
      · dsimp only; split <;> simp_all
      · dsimp only; split <;> simp_all
    · simp only [ite_eq_right hi] at hs
      cases hs

/-- Every actual comparison transition retains complete operand tapes,
including cells outside the scanned words. -/
theorem step_operands {c d : Config 3 4 a} (hs : Machine.step (program a) c = some d)
    (i : Fin 3) (hi : i ≠ 2) : d.tape i = c.tape i := by
  have hn : c.state ≠ 3 := by intro he; simp [Machine.step,program,he] at hs
  simp only [Machine.step,program,ite_eq_right hn] at hs
  by_cases hb : c.tape 0 (c.head 0) = blank ∧ c.tape 1 (c.head 1) = blank
  · simp only [ite_eq_left hb,Option.some.injEq] at hs
    subst d
    funext z
    dsimp only
    simp only [ite_eq_right hi]
    split_ifs with he
    · rw [he]
    · rfl
  · simp only [ite_eq_right hb] at hs
    by_cases hv : isInput (c.tape 0 (c.head 0)) ∧ isInput (c.tape 1 (c.head 1))
    · simp only [ite_eq_left hv,Option.some.injEq] at hs
      subst d
      funext z
      change (if z = c.head i then c.tape i (c.head i) else c.tape i z) = c.tape i z
      split_ifs with he
      · rw [he]
      · rfl
    · simp only [ite_eq_right hv] at hs
      cases hs

/-- The operand frame and head bounds belong to the same actual run. -/
theorem run_operands {c d : Config 3 4 a} {k : ℕ}
    (hrun : Machine.run (program a) k c = some d) (i : Fin 3) (hi : i ≠ 2) :
    d.tape i = c.tape i := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst d; rfl
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (program a) c with
    | none => simp [hs] at hrun
    | some e =>
      rw [hs,Option.bind_some] at hrun
      exact (ih hrun).trans (step_operands hs i hi)

/-- The invariant holds at every prefix, including the terminal prefix. -/
theorem HeadBounds.run {lo₀ hi₀ lo₁ hi₁ r : ℤ} {c c' : Config 3 4 a}
    (h : HeadBounds lo₀ hi₀ lo₁ hi₁ r c) {k : ℕ}
    (hrun : run (program a) k c = some c') : HeadBounds lo₀ hi₀ lo₁ hi₁ r c' := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst c'; exact h
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (program a) c with
    | none => simp [hs] at hrun
    | some c₁ =>
      rw [hs,Option.bind_some] at hrun
      exact ih (h.step hs) hrun

/-- The two scanned words may have arbitrary contents between their starts
and blank endpoints. -/
theorem HeadBounds.of_cfg (f g out : ℤ → Fin (a+4)) (p q r : ℤ) (n m : ℕ)
    (hf : f (p+n) = blank) (hg : g (q+m) = blank) :
    HeadBounds p (p+n) q (q+m) r (cfg f g out p q r 0) := by
  constructor
  · simp [cfg]
  · simp [cfg]
  · simp [cfg]
  · intro _; rfl
  · exact hf
  · exact hg

theorem HeadBounds.heads {lo₀ hi₀ lo₁ hi₁ r : ℤ} {c : Config 3 4 a}
    (h : HeadBounds lo₀ hi₀ lo₁ hi₁ r c) :
    ∀ i, (![lo₀,lo₁,r] : Fin 3 → ℤ) i ≤ c.head i ∧
      c.head i ≤ (![hi₀,hi₁,r+1] : Fin 3 → ℤ) i := by
  intro i
  fin_cases i
  · exact h.left
  · exact h.right
  · exact h.result

end IntegerMultBounds.Machine.BinaryCompare

module

public import IntegerMultBounds.Machine.DescriptorStackControl

/-! Fixed storage intervals for delimiter-directed descriptor scans. The marker
at the approached endpoint prevents escape; all tape contents are preserved. -/
@[expose] public section
namespace IntegerMultBounds.Machine.DescriptorStackControl
variable {t a : ℕ}

structure SeekBounds (focus : Fin t) (stop : Fin (a+4)) (move : Move)
    (lo hi : Fin t → ℤ) (c : Config t 1 a) : Prop where
  heads : ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i
  leftStop : move = .left → c.tape focus (lo focus) = stop
  rightStop : move = .right → c.tape focus (hi focus) = stop

theorem SeekBounds.step {focus : Fin t} {stop : Fin (a+4)} {move : Move}
    {lo hi : Fin t → ℤ} {c c' : Config t 1 a}
    (h : SeekBounds focus stop move lo hi c)
    (hs : step (seek focus stop move) c = some c') :
    SeekBounds focus stop move lo hi c' := by
  have hn : c.tape focus (c.head focus) ≠ stop := by
    intro he
    simp [Machine.step,seek,he] at hs
  have hl : move = .left → lo focus < c.head focus := by
    intro hm
    have hb := h.heads focus
    have he := h.leftStop hm
    by_contra hx
    have hh : c.head focus = lo focus := by omega
    exact hn (hh ▸ he)
  have hr : move = .right → c.head focus < hi focus := by
    intro hm
    have hb := h.heads focus
    have he := h.rightStop hm
    by_contra hx
    have hh : c.head focus = hi focus := by omega
    exact hn (hh ▸ he)
  simp only [Machine.step,seek,ite_eq_right hn,Option.some.injEq] at hs
  subst c'
  have htape : (fun i z => if z = c.head i then c.tape i (c.head i) else c.tape i z) = c.tape := by
    funext i z
    split_ifs with he
    · rw [he]
    · rfl
  constructor
  · intro i
    change lo i ≤ c.head i+(if i = focus then move else Move.stay).offset ∧
      c.head i+(if i = focus then move else Move.stay).offset ≤ hi i
    by_cases he : i = focus
    · subst i
      simp only [ite_true]
      have hb := h.heads focus
      cases move with
      | left => have hh := hl rfl; simp only [Move.offset]; omega
      | stay => simpa only [Move.offset,add_zero] using hb
      | right => have hh := hr rfl; simp only [Move.offset]; omega
    · simpa only [ite_eq_right he,Move.offset,add_zero] using h.heads i
  · change move = .left → (if lo focus = c.head focus then c.tape focus (c.head focus) else c.tape focus (lo focus)) = stop
    change move = .left → (fun i z => if z = c.head i then c.tape i (c.head i) else c.tape i z) focus (lo focus) = stop
    rw [htape]
    exact h.leftStop
  · change move = .right → (fun i z => if z = c.head i then c.tape i (c.head i) else c.tape i z) focus (hi focus) = stop
    rw [htape]
    exact h.rightStop

theorem SeekBounds.run {focus : Fin t} {stop : Fin (a+4)} {move : Move}
    {lo hi : Fin t → ℤ} {c c' : Config t 1 a} {k : ℕ}
    (h : SeekBounds focus stop move lo hi c)
    (hrun : run (seek focus stop move) k c = some c') :
    SeekBounds focus stop move lo hi c' := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst c'; exact h
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (seek focus stop move) c with
    | none => simp [hs] at hrun
    | some c₁ =>
      rw [hs,Option.bind_some] at hrun
      exact ih (h.step hs) hrun

end IntegerMultBounds.Machine.DescriptorStackControl

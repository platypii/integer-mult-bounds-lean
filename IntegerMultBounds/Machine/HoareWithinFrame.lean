module

public import IntegerMultBounds.Machine.HoareWithin
public import IntegerMultBounds.Machine.RunWithinFrame

/-! A bounded halting contract extends over a stationary complementary bank. -/
@[expose] public section
namespace IntegerMultBounds.Machine.HoareWithin
variable {t s q a B : ℕ} {M : Program t q a}

theorem extend_eq {v w : Tapes t a} (extra : Tapes s a) {H : TapePred (t+s) a}
    (h : HoareWithin M (· = v) (· = w) B (fun z => H (z.append extra))) :
    HoareWithin (Machine.extend M s) (· = v.append extra) (· = w.append extra) B H := by
  intro input hi
  subst input
  obtain ⟨n,hn,c,hr,hh,hp⟩ := h v rfl
  refine ⟨n,hn,c.extend extra,hr.extend extra,extend_halt M extra hh,?_⟩
  change c.tapes.append extra = w.append extra
  rw [hp]

theorem extend_heads_eq {v w : Tapes t a} (extra : Tapes s a) (lo hi : ℤ)
    (h : HoareWithin M (· = v) (· = w) B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (hframe : ∀ j, lo ≤ extra.head j ∧ extra.head j ≤ hi) :
    HoareWithin (Machine.extend M s) (· = v.append extra) (· = w.append extra) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  apply extend_eq extra
  apply h.consequence (fun _ h => h) (fun _ h => h) le_rfl
  intro z hz j
  induction j using Fin.addCases with
  | left j => simpa only [Tapes.append,Fin.addCases_left] using hz j
  | right j => simpa only [Tapes.append,Fin.addCases_right] using hframe j

end IntegerMultBounds.Machine.HoareWithin

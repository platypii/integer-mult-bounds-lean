module

public import IntegerMultBounds.Machine.RunInvariant

/-! A concrete finite run with a tape predicate at every prefix. Composition
reuses a common allowance; it never adds allowances across successive phases. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ}

def RunWithin (M : Program t q a) (H : TapePred t a) (n : ℕ) (c d : Config t q a) : Prop :=
  run M n c = some d ∧ ∀ m ≤ n, ∀ z, run M m c = some z → H z.tapes

namespace RunWithin
variable {M : Program t q a} {H J : TapePred t a} {n m : ℕ} {c d z : Config t q a}

theorem initial (h : RunWithin M H n c d) : H c.tapes := h.2 0 (Nat.zero_le _) c rfl

theorem finish (h : RunWithin M H n c d) : H d.tapes := h.2 n le_rfl d h.1

theorem refl (hc : H c.tapes) : RunWithin M H 0 c c := by
  refine ⟨rfl,?_⟩
  intro m hm z hz
  have : m = 0 := by omega
  subst m
  simp only [run,Option.some.injEq] at hz
  subst z
  exact hc

theorem single (hs : step M c = some d) (hc : H c.tapes) (hd : H d.tapes) :
    RunWithin M H 1 c d := by
  refine ⟨by simpa only [run_one] using hs,?_⟩
  intro m hm z hz
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · simp only [run,Option.some.injEq] at hz
    subst z; exact hc
  · simp only [run_one,hs,Option.some.injEq] at hz
    subst z; exact hd

theorem mono (h : RunWithin M H n c d) (hHJ : ∀ v, H v → J v) : RunWithin M J n c d :=
  ⟨h.1,fun m hm z hz => hHJ _ (h.2 m hm z hz)⟩

theorem trans (h : RunWithin M H n c d) (h' : RunWithin M H m d z) :
    RunWithin M H (n+m) c z := by
  refine ⟨by rw [run_add,h.1,Option.bind_some,h'.1],?_⟩
  intro k hk x hx
  by_cases hkn : k ≤ n
  · exact h.2 k hkn x hx
  · have he : k = n+(k-n) := by omega
    rw [he,run_add,h.1,Option.bind_some] at hx
    exact h'.2 (k-n) (by omega) x hx

/-- Step simulations preserve all intermediate configurations, not just endpoints. -/
theorem simulation {u r b : ℕ} {N : Program u r b} {G : TapePred u b}
    (f : Config t q a → Config u r b)
    (hstep : ∀ c d, step M c = some d → step N (f c) = some (f d))
    (hH : ∀ c, H c.tapes → G (f c).tapes) (h : RunWithin M H n c d) :
    RunWithin N G n (f c) (f d) := by
  refine ⟨run_simulation M N f hstep h.1,?_⟩
  intro m hm z hz
  have he : n = m+(n-m) := by omega
  have hr := h.1
  rw [he,run_add] at hr
  cases hx : run M m c with
  | none => simp [hx] at hr
  | some x =>
    have hs := run_simulation M N f hstep hx
    rw [hs,Option.some.injEq] at hz
    subst z
    exact hH x (h.2 m hm x hx)

/-- A bounded halting witness certifies every actual reachable prefix. -/
theorem prefix_of_halt (h : RunWithin M H n c d) (hh : step M d = none)
    (hr : run M m c = some z) : H z.tapes :=
  h.2 m (run_length_le_of_halt hr h.1 hh) z hr

end RunWithin
end IntegerMultBounds.Machine

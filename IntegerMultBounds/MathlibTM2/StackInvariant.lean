module

public import IntegerMultBounds.MathlibTM2.Stack

/-! Structured executions carrying an invariant at every intermediate store.
The depth index counts outstanding calls, so resource invariants can charge the
compiled return stack as well as the data stacks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack

variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]

/-- Execution with a store invariant, indexed by the number of outstanding calls. -/
inductive ExecWithin (body : P → Prog P Γ σ) (Inv : ℕ → Store Γ σ → Prop) :
    ℕ → Prog P Γ σ → Store Γ σ → ℕ → Store Γ σ → Prop
  | act {d} (a : Action Γ σ) (s : Store Γ σ) : Inv d s → Inv d (a.run s) →
      ExecWithin body Inv d (.act a) s 1 (a.run s)
  | seq {d p q s t u m n} : ExecWithin body Inv d p s m t → ExecWithin body Inv d q t n u →
      ExecWithin body Inv d (.seq p q) s (m+n) u
  | cond_true {d f p q s t n} : f s.var = true → ExecWithin body Inv d p s n t →
      ExecWithin body Inv d (.cond f p q) s (n+1) t
  | cond_false {d f p q s t n} : f s.var = false → ExecWithin body Inv d q s n t →
      ExecWithin body Inv d (.cond f p q) s (n+1) t
  | loop_false {d f p s} : f s.var = false → Inv d s → ExecWithin body Inv d (.loop f p) s 1 s
  | loop_true {d f p s t u m n} : f s.var = true → ExecWithin body Inv d p s m t →
      ExecWithin body Inv d (.loop f p) t n u → ExecWithin body Inv d (.loop f p) s (m+n+1) u
  | call {d f s t n} : Inv d s → ExecWithin body Inv (d+1) (body f) s n t → Inv d t →
      ExecWithin body Inv d (.call f) s (n+2) t

namespace ExecWithin

variable {body : P → Prog P Γ σ} {Inv J : ℕ → Store Γ σ → Prop}
  {d : ℕ} {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ}

theorem toExec (h : ExecWithin body Inv d p s n t) : Exec body p s n t := by
  induction h with
  | act a s _ _ => exact Exec.act a s
  | seq _ _ hp hq => exact Exec.seq hp hq
  | cond_true hf _ hp => exact Exec.cond_true hf hp
  | cond_false hf _ hp => exact Exec.cond_false hf hp
  | loop_false hf _ => exact Exec.loop_false hf
  | loop_true hf _ _ hp hq => exact Exec.loop_true hf hp hq
  | call _ _ _ hp => exact Exec.call hp

/-- Regroup sequential stages without changing their invariant or step count. -/
theorem seq_assoc {q r : Prog P Γ σ}
    (h : ExecWithin body Inv d (.seq (.seq p q) r) s n t) :
    ExecWithin body Inv d (.seq p (.seq q r)) s n t := by
  cases h with
  | seq hpq hr =>
    cases hpq with
    | seq hp hq => simpa only [Nat.add_assoc] using ExecWithin.seq hp (ExecWithin.seq hq hr)

theorem mono (h : ExecWithin body Inv d p s n t) (hIJ : ∀ d s, Inv d s → J d s) :
    ExecWithin body J d p s n t := by
  induction h with
  | act a s hi ho => exact .act a s (hIJ _ _ hi) (hIJ _ _ ho)
  | seq _ _ hp hq => exact .seq hp hq
  | cond_true hf _ hp => exact .cond_true hf hp
  | cond_false hf _ hp => exact .cond_false hf hp
  | loop_false hf hi => exact .loop_false hf (hIJ _ _ hi)
  | loop_true hf _ _ hp hq => exact .loop_true hf hp hq
  | call hi _ ho hp => exact .call (hIJ _ _ hi) hp (hIJ _ _ ho)

theorem initial (h : ExecWithin body Inv d p s n t) : Inv d s := by
  induction h with
  | act _ _ hi _ => exact hi
  | seq _ _ hp _ => exact hp
  | cond_true _ _ hp => exact hp
  | cond_false _ _ hp => exact hp
  | loop_false _ hi => exact hi
  | loop_true _ _ _ hp _ => exact hp
  | call hi _ _ _ => exact hi

theorem final (h : ExecWithin body Inv d p s n t) : Inv d t := by
  induction h with
  | act _ _ _ ho => exact ho
  | seq _ _ _ hq => exact hq
  | cond_true _ _ hp => exact hp
  | cond_false _ _ hp => exact hp
  | loop_false _ hi => exact hi
  | loop_true _ _ _ _ hq => exact hq
  | call _ _ ho _ => exact ho

end ExecWithin
end IntegerMultBounds.MathlibTM2.Stack

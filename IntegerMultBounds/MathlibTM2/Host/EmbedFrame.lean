module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Host.StackFrame
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Structural footprints of embedded closed programs. The existing frame rule
and execution uniqueness certify untouched stacks without replaying execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type} [DecidableEq K]

theorem Exec.preserves_stack {body : P → Prog P Γ σ} {p : Prog P Γ σ}
    {s t : Store Γ σ} {n : ℕ} (he : Exec body p s n t) (k : K)
    (hp : programOn (fun j => j ≠ k) p) : t.stk k = s.stk k := by
  have hstart : frameStore (fun j => j ≠ k) s.stk s = s := by
    ext1
    · rfl
    · funext j
      simp [frameStore]
  have hf := he.frame hp s.stk
  rw [hstart] at hf
  have ht := (he.unique hf).2
  have hh := congrArg (fun z : Store Γ σ => z.stk k) ht
  simpa [frameStore] using hh

end IntegerMultBounds.MathlibTM2.Stack
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
variable {T T' Q A : ℕ} {U P' : Type}

theorem embAct_on (e : Fin T → Fin T') (allowed : HK T' → Prop)
    (hallowed : ∀ k, allowed (embK e k)) (a : Act T Q A U) : actionOn allowed (embAct e a) := by
  induction a with
  | done => trivial
  | push k f a ih | peek k f a ih | pop k f a ih => exact ⟨hallowed k,ih⟩
  | load f a ih => exact ih
  | branch f a b iha ihb => exact ⟨iha,ihb⟩

theorem embProg_empty_on (e : Fin T → Fin T') (ι : Empty → P') (allowed : HK T' → Prop)
    (hallowed : ∀ k, allowed (embK e k)) (p : Pr Empty T Q A U) :
    programOn allowed (embProg e ι p) := by
  induction p with
  | act a => exact embAct_on e allowed hallowed a
  | seq p q hp hq | cond f p q hp hq => exact ⟨hp,hq⟩
  | loop f p hp => exact hp
  | call f => exact nomatch f

/-- A placed closed program never accesses an external right stack. -/
theorem embProg_empty_avoids_right (e : Fin T → Fin T') (ι : Empty → P') (dst : Fin T')
    (hoff : ∀ i, e i ≠ dst) (p : Pr Empty T Q A U) :
    programOn (fun k => k ≠ HK.rt dst) (embProg e ι p) := by
  apply embProg_empty_on
  intro k
  cases k <;> simp [embK,hoff]

end IntegerMultBounds.MathlibTM2.Host

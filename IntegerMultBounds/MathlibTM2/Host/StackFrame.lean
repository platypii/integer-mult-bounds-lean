module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-! A structural frame rule for call-free stack programs. Stacks outside the
program's footprint may contain arbitrary data, without changing execution time. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type} [DecidableEq K]

def actionOn (allowed : K → Prop) : Action Γ σ → Prop
  | .done => True
  | .push k _ a | .peek k _ a | .pop k _ a => allowed k ∧ actionOn allowed a
  | .load _ a => actionOn allowed a
  | .branch _ a b => actionOn allowed a ∧ actionOn allowed b

def programOn (allowed : K → Prop) : Prog P Γ σ → Prop
  | .act a => actionOn allowed a
  | .seq p q | .cond _ p q => programOn allowed p ∧ programOn allowed q
  | .loop _ p => programOn allowed p
  | .call _ => False

def frameStore (allowed : K → Prop) [DecidablePred allowed]
    (extra : ∀ k, List (Γ k)) (s : Store Γ σ) : Store Γ σ :=
  ⟨s.var,fun k => if allowed k then s.stk k else extra k⟩

theorem frameStore_update (allowed : K → Prop) [DecidablePred allowed]
    (extra : ∀ k, List (Γ k)) (s : Store Γ σ) (k : K) (hk : allowed k) (xs : List (Γ k)) :
    frameStore allowed extra {s with stk := Function.update s.stk k xs} =
      {frameStore allowed extra s with stk := Function.update (frameStore allowed extra s).stk k xs} := by
  refine Store.ext rfl ?_
  funext j
  by_cases hj : j = k
  · subst j; simp [frameStore,hk]
  · simp [frameStore,hj]

theorem actionOn_run {allowed : K → Prop} [DecidablePred allowed]
    (extra : ∀ k, List (Γ k)) (a : Action Γ σ) (ha : actionOn allowed a) (s : Store Γ σ) :
    a.run (frameStore allowed extra s) = frameStore allowed extra (a.run s) := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih =>
    have hh := ih ha.2 ⟨s.var,Function.update s.stk k (f s.var::s.stk k)⟩
    rw [frameStore_update allowed extra _ k ha.1] at hh
    simpa only [Action.run,frameStore,ha.1,ite_true] using hh
  | peek k f a ih =>
    simpa only [Action.run,frameStore,ha.1,ite_true] using ih ha.2 ⟨f s.var (s.stk k).head?,s.stk⟩
  | pop k f a ih =>
    have hh := ih ha.2 ⟨f s.var (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
    rw [frameStore_update allowed extra {s with var := f s.var (s.stk k).head?} k ha.1] at hh
    simpa only [Action.run,frameStore,ha.1,ite_true] using hh
  | load f a ih =>
    simpa only [Action.run,frameStore] using ih ha ⟨f s.var,s.stk⟩
  | branch f a b iha ihb =>
    cases hf : f s.var
    · simpa only [Action.run,frameStore,hf,Bool.false_eq_true,ite_false] using ihb ha.2 s
    · simpa only [Action.run,frameStore,hf,ite_true] using iha ha.1 s

/-- Framing preserves the exact local state and exact step count. -/
theorem Exec.frame {body : P → Prog P Γ σ} {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ}
    (he : Exec body p s n t) {allowed : K → Prop} [DecidablePred allowed]
    (hp : programOn allowed p) (extra : ∀ k, List (Γ k)) :
    Exec body p (frameStore allowed extra s) n (frameStore allowed extra t) := by
  induction he with
  | act a s =>
    have hh := Exec.act (body := body) a (frameStore allowed extra s)
    rwa [actionOn_run extra a hp] at hh
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ hp.1) (ih₂ hp.2)
  | cond_true hf _ ih => exact .cond_true hf (ih hp.1)
  | cond_false hf _ ih => exact .cond_false hf (ih hp.2)
  | loop_false hf => exact .loop_false hf
  | loop_true hf _ _ ih₁ ih₂ => exact .loop_true hf (ih₁ hp) (ih₂ hp)
  | call _ _ => exact False.elim hp

end IntegerMultBounds.MathlibTM2.Stack

namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
variable {T Q A : ℕ} {P U : Type}

/-- Left stacks are spectators for programs accessing only the other stacks. -/
def nonLeft : HK T → Prop
  | .lt _ => False
  | _ => True

instance : DecidablePred (nonLeft (T := T)) := fun k => by cases k <;> simp [nonLeft] <;> infer_instance

def leftFrame (L : Fin T → List (Fin (A+4))) : ∀ k : HK T, List (HΓ A k)
  | .lt i => L i
  | _ => []

theorem frameStore_mk (v : HS T Q A U) (S : Stacks T A) (L : Fin T → List (Fin (A+4))) :
    frameStore nonLeft (leftFrame L) (mk v S) = mk v {S with L := L} := by
  refine Store.ext rfl ?_
  funext k
  cases k <;> rfl

theorem exec_withLeft {body : P → Pr P T Q A U} {p : Pr P T Q A U}
    {v v' : HS T Q A U} {S S' : Stacks T A} {n : ℕ}
    (he : Exec body p (mk v S) n (mk v' S')) (hp : programOn nonLeft p)
    (L : Fin T → List (Fin (A+4))) :
    Exec body p (mk v {S with L := L}) n (mk v' {S' with L := L}) := by
  simpa only [frameStore_mk] using he.frame hp (leftFrame L)

end IntegerMultBounds.MathlibTM2.Host

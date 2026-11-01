module

public import IntegerMultBounds.MathlibTM2.Host.EmbedFrame

/-! Register ownership frames both stacks of every external register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type}

theorem actionOn_mono {allowed allowed' : K → Prop} {a : Action Γ σ}
    (h : actionOn allowed a) (hf : ∀ k, allowed k → allowed' k) : actionOn allowed' a := by
  induction a with
  | done => trivial
  | push k f a ih | peek k f a ih | pop k f a ih => exact ⟨hf k h.1,ih h.2⟩
  | load f a ih => exact ih h
  | branch f a b iha ihb => exact ⟨iha h.1,ihb h.2⟩

theorem programOn_mono {allowed allowed' : K → Prop} {p : Prog P Γ σ}
    (h : programOn allowed p) (hf : ∀ k, allowed k → allowed' k) : programOn allowed' p := by
  induction p with
  | act a => exact actionOn_mono h hf
  | seq p q hp hq | cond f p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | loop f p hp => exact hp h
  | call f => exact h

end IntegerMultBounds.MathlibTM2.Stack
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
variable {T T' Q A : ℕ} {P U : Type}

def registersOn (allowed : Fin T → Prop) : HK T → Prop
  | .lt i | .rt i => allowed i
  | _ => True

theorem embProg_empty_on_registers (e : Fin T → Fin T') (ι : Empty → P)
    (allowed : Fin T' → Prop) (hallowed : ∀ i, allowed (e i)) (p : Pr Empty T Q A U) :
    programOn (registersOn allowed) (embProg e ι p) := by
  apply embProg_empty_on
  intro k
  cases k <;> simp [embK,registersOn,hallowed]

theorem registersOn_avoids_left {allowed : Fin T → Prop} {p : Pr P T Q A U}
    (h : programOn (registersOn allowed) p) (outside : Fin T) (hoff : ¬allowed outside) :
    programOn (fun k => k ≠ HK.lt outside) p := by
  apply programOn_mono h
  intro k hk he
  subst k
  exact hoff hk

theorem registersOn_avoids_right {allowed : Fin T → Prop} {p : Pr P T Q A U}
    (h : programOn (registersOn allowed) p) (outside : Fin T) (hoff : ¬allowed outside) :
    programOn (fun k => k ≠ HK.rt outside) p := by
  apply programOn_mono h
  intro k hk he
  subst k
  exact hoff hk

end IntegerMultBounds.MathlibTM2.Host

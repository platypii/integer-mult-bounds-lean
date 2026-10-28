module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! The structured store invariant holds throughout the compiled execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
open Turing
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]

/-- A counted machine trace with an invariant at every configuration. -/
inductive ReachWithin {Λ σ' : Type} {Γ' : Option K → Type}
    (M : Λ → TM2.Stmt Γ' Λ σ') (Inv : TM2.Cfg Γ' Λ σ' → Prop)
    (c : TM2.Cfg Γ' Λ σ') : ℕ → TM2.Cfg Γ' Λ σ' → Prop
  | refl : Inv c → ReachWithin M Inv c 0 c
  | step {t u n} : ReachWithin M Inv c n t → TM2.step M t = some u → Inv u →
      ReachWithin M Inv c (n+1) u

namespace ReachWithin
variable {Λ σ' : Type} {Γ' : Option K → Type}
  {M : Λ → TM2.Stmt Γ' Λ σ'} {Inv : TM2.Cfg Γ' Λ σ' → Prop}
  {c t u : TM2.Cfg Γ' Λ σ'} {m n : ℕ}

theorem single (hi : Inv c) (ho : Inv t) (hs : TM2.step M c = some t) :
    ReachWithin M Inv c 1 t := .step (.refl hi) hs ho

theorem trans (h : ReachWithin M Inv c m t) (g : ReachWithin M Inv t n u) :
    ReachWithin M Inv c (m+n) u := by
  induction g with
  | refl _ => simpa using h
  | step _ hs hi ih => simpa only [Nat.add_assoc] using ih.step hs hi

theorem toReach (h : ReachWithin M Inv c n t) : Reach M c n t := by
  induction h with
  | refl _ => rfl
  | step _ hs _ ih => exact ih.trans (Reach.single hs)

theorem mono {J : TM2.Cfg Γ' Λ σ' → Prop} (h : ReachWithin M Inv c n t)
    (hIJ : ∀ z, Inv z → J z) : ReachWithin M J c n t := by
  induction h with
  | refl hi => exact .refl (hIJ _ hi)
  | step _ hs hi ih => exact .step ih hs (hIJ _ hi)

/-- In particular, every prefix of the deterministic machine run satisfies the invariant. -/
theorem at_prefix (h : ReachWithin M Inv c n t) :
    ∀ j ≤ n, ∀ z, Reach M c j z → Inv z := by
  induction h with
  | refl hi =>
    intro j hj z hz
    have : j = 0 := by omega
    subst j
    have : c = z := by simpa only [Reach,Function.iterate_zero, id_eq,Option.some.injEq] using hz
    simpa [← this] using hi
  | @step t u n h hs hu ih =>
    intro j hj z hz
    by_cases hjn : j ≤ n
    · exact ih j hjn z hz
    · have hj : j = n+1 := by omega
      subst j
      have he := (h.step hs hu).toReach
      have : z = u := Option.some.inj (hz.symm.trans he)
      simpa [this] using hu

end ReachWithin

/-- Decode the ordinary data stacks and the actual compiled return-stack length. -/
def compiledInv (body : P → Prog P Γ σ) (Inv : ℕ → Store Γ σ → Prop)
    (c : TM2.Cfg (MΓ body) (Lbl body) (Mσ body)) : Prop :=
  Inv (c.stk none).length ⟨c.var.1,fun k => c.stk (some k)⟩

omit [DecidableEq K] in
@[simp] theorem compiledInv_cfg (body : P → Prog P Γ σ) (Inv : ℕ → Store Γ σ → Prop)
    (l s x R) : compiledInv body Inv (cfg l s x R) = Inv R.length s := rfl

variable {body : P → Prog P Γ σ} {Inv : ℕ → Store Γ σ → Prop} {d : ℕ}

theorem ExecWithin.sim {main : P} {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ} (h : ExecWithin body Inv d p s n t) :
    ∀ (embed : p.Labels → Lbl body) (exit : Option (Lbl body)),
      (∀ l, mcode body main (embed l) = Prog.code body p embed exit l) →
      ∀ x R, R.length = d → ∃ y, ReachWithin (mcode body main) (compiledInv body Inv) (cfg (some (embed p.start)) s x R) n (cfg exit t y R) := by
  induction h with
  | act a s hi ho =>
      intro embed exit hc x R hR
      refine ⟨x, ReachWithin.single (by simpa [hR] using hi) (by simpa [hR] using ho) ?_⟩
      simp only [cfg, TM2.step, hc, Prog.code, Action.lift_stepAux, stepAux_jump]
  | @seq d p q s t u m n _ _ ihp ihq =>
      intro embed exit hc x R hR
      obtain ⟨y, hy⟩ := ihp (fun l => embed (.inl l)) (some (embed (.inr q.start)))
        (fun l => hc (.inl l)) x R hR
      obtain ⟨z, hz⟩ := ihq (fun l => embed (.inr l)) exit (fun l => hc (.inr l)) y R hR
      exact ⟨z, hy.trans hz⟩
  | @cond_true d f p q s t n hf he ih =>
      intro embed exit hc x R hR
      obtain ⟨y, hy⟩ := ih (fun l => embed (.inr (.inl l))) exit (fun l => hc (.inr (.inl l))) x R hR
      refine ⟨y, Nat.add_comm n 1 ▸ (ReachWithin.single (by simpa [hR] using he.initial) (by simpa [hR] using he.initial) ?_).trans hy⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf]
      rfl
  | @cond_false d f p q s t n hf he ih =>
      intro embed exit hc x R hR
      obtain ⟨y, hy⟩ := ih (fun l => embed (.inr (.inr l))) exit (fun l => hc (.inr (.inr l))) x R hR
      refine ⟨y, Nat.add_comm n 1 ▸ (ReachWithin.single (by simpa [hR] using he.initial) (by simpa [hR] using he.initial) ?_).trans hy⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf]
      rfl
  | @loop_false d f p s hf hi =>
      intro embed exit hc x R hR
      refine ⟨x, ReachWithin.single (by simpa [hR] using hi) (by simpa [hR] using hi) ?_⟩
      simp only [cfg, TM2.step]
      rw [hc]
      simp only [Prog.start, Prog.code, TM2.stepAux, hf, stepAux_jump]
      rfl
  | @loop_true d f p s t u m n hf he _ ihp ihl =>
      intro embed exit hc x R hR
      obtain ⟨y, hy⟩ := ihp (fun l => embed (.inr l)) (some (embed (.inl ())))
        (fun l => hc (.inr l)) x R hR
      obtain ⟨z, hz⟩ := ihl embed exit hc y R hR
      refine ⟨z, ?_⟩
      have h₀ : ReachWithin (mcode body main) (compiledInv body Inv) (cfg (some (embed (Prog.loop f p).start)) s x R) 1
          (cfg (some (embed (.inr p.start))) s x R) := by
        apply ReachWithin.single (by simpa [hR] using he.initial) (by simpa [hR] using he.initial)
        simp only [cfg, TM2.step]
        rw [hc]
        simp only [Prog.start, Prog.code, TM2.stepAux, hf]
        rfl
      have := h₀.trans (hy.trans hz)
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  | @call d f s t n hi he ho ih =>
      intro embed exit hc x R hR
      obtain ⟨y, hy⟩ := ih (Lbl.node f) (some .ret) (fun _ => rfl) x (exit :: R) (by simp [hR])
      have h₀ : ReachWithin (mcode body main) (compiledInv body Inv) (cfg (some (embed (Prog.call f).start)) s x R) 1
          (cfg (some (.node f (body f).start)) s x (exit :: R)) := by
        apply ReachWithin.single (by simpa [hR] using hi) (by simpa [hR] using he.initial)
        simp only [cfg, TM2.step]
        rw [hc]
        simp only [Prog.code, TM2.stepAux]
        rw [show mstk (body := body) s.stk R none = R from rfl, mstk_update_none]
        rfl
      cases exit with
      | none =>
          refine ⟨none, ?_⟩
          have h₁ : ReachWithin (mcode body main) (compiledInv body Inv) (cfg (some .ret) t y (none :: R)) 1 (cfg none t none R) := by
            apply ReachWithin.single (by simpa [hR] using he.final) (by simpa [hR] using ho)
            simp only [cfg, TM2.step, mcode, TM2.stepAux]
            rw [show mstk (body := body) t.stk (none :: R) none = none :: R from rfl,
              mstk_update_none]
            rfl
          simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₀.trans (hy.trans h₁)
      | some l =>
          refine ⟨some (some l), ?_⟩
          have h₁ : ReachWithin (mcode body main) (compiledInv body Inv) (cfg (some .ret) t y (some l :: R)) 1
              (cfg (some l) t (some (some l)) R) := by
            apply ReachWithin.single (by simpa [hR] using he.final) (by simpa [hR] using ho)
            simp only [cfg, TM2.step, mcode, TM2.stepAux]
            rw [show mstk (body := body) t.stk (some l :: R) none = some l :: R from rfl,
              mstk_update_none]
            rfl
          simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₀.trans (hy.trans h₁)


section Stock
variable [Fintype K]
open IntegerMultBounds.MathlibTM2.Fast.Main

/-- All compiled stacks, including the return stack. -/
def compiledSize (body : P → Prog P Γ σ)
    (c : TM2.Cfg (MΓ body) (Lbl body) (Mσ body)) : ℕ :=
  ∑ k, (c.stk k).length

@[simp] theorem compiledSize_cfg (l s x R) :
    compiledSize body (cfg l s x R) = mnSize s+R.length := by
  simp [compiledSize,Fintype.sum_option,cfg,mstk,mnSize,Nat.add_comm]
  rfl

theorem compiledInv_stock (B : ℕ) (c : TM2.Cfg (MΓ body) (Lbl body) (Mσ body)) :
    compiledInv body (fun d z => mnSize z+d ≤ B) c ↔ compiledSize body c ≤ B := by
  simp [compiledInv,compiledSize,mnSize,Fintype.sum_option,Nat.add_comm]
  rfl

/-- Transfer a stock certificate to every configuration of the compiled subprogram. -/
theorem ExecWithin.stock_sim {main : P} {p : Prog P Γ σ} {s t : Store Γ σ} {n d B : ℕ}
    (h : ExecWithin body (fun depth z => mnSize z+depth ≤ B) d p s n t)
    (embed : p.Labels → Lbl body) (exit : Option (Lbl body))
    (hc : ∀ l, mcode body main (embed l) = Prog.code body p embed exit l)
    (x R) (hR : R.length = d) :
    ∃ y, ReachWithin (mcode body main) (fun c => compiledSize body c ≤ B)
      (cfg (some (embed p.start)) s x R) n (cfg exit t y R) := by
  obtain ⟨y,hy⟩ := h.sim embed exit hc x R hR
  exact ⟨y,hy.mono (fun c hc => (compiledInv_stock B c).mp hc)⟩

/-- Include the entry push and final return as well as the complete main execution. -/
theorem ExecWithin.stock_run_main {main : P} {s t : Store Γ σ} {n B : ℕ}
    (h : ExecWithin body (fun depth z => mnSize z+depth ≤ B) 1 (body main) s n t) :
    ReachWithin (mcode body main) (fun c => compiledSize body c ≤ B)
      (cfg (some .entry) s none []) (n+2) (cfg none t none []) := by
  obtain ⟨y,hy⟩ := h.stock_sim (Lbl.node main) (some .ret) (fun _ => rfl) none [none] rfl
  have hi := h.initial
  have ho := h.final
  have h₀ : ReachWithin (mcode body main) (fun c => compiledSize body c ≤ B)
      (cfg (some .entry) s none []) 1
      (cfg (some (.node main (body main).start)) s none [none]) := by
    apply ReachWithin.single (by simp; omega) (by simpa using hi)
    simp only [cfg, TM2.step, mcode, TM2.stepAux]
    rw [show mstk (body := body) s.stk [] none = [] from rfl,mstk_update_none]
    rfl
  have h₁ : ReachWithin (mcode body main) (fun c => compiledSize body c ≤ B)
      (cfg (some .ret) t y [none]) 1 (cfg none t none []) := by
    apply ReachWithin.single (by simpa using ho) (by simp; omega)
    simp only [cfg, TM2.step, mcode, TM2.stepAux]
    rw [show mstk (body := body) t.stk [none] none = [none] from rfl,mstk_update_none]
    rfl
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h₀.trans (hy.trans h₁)

end Stock

end IntegerMultBounds.MathlibTM2.Stack

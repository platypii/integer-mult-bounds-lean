import IntegerMultBounds.Schoenhage.Ops

/-! Word programs moved into a larger bank: an injective map of tape names
relabels every primitive slot, loop tape and branch tape. An execution of the
relabelled program from a bank whose relabelled tapes hold the original bank
ends in a bank whose relabelled tapes hold the original result, with the same
cost, and every tape outside the image untouched (`Exec.map`, `Runs.map`). -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t t' : ℕ}

/-- Relabel the tapes of a word program. -/
def Cmd.map (f : Fin t → Fin t') (hf : Function.Injective f) : Cmd a t → Cmd a t'
  | .prim P slot hinj => .prim P (f ∘ slot) (hf.comp hinj)
  | .seq c d => .seq (c.map f hf) (d.map f hf)
  | .loop i b => .loop (f i) (b.map f hf)
  | .cond i c d => .cond (f i) (c.map f hf) (d.map f hf)

theorem upd_comp {s : ℕ} (f : Fin t → Fin t') (hf : Function.Injective f) (τ : Fin t' → WTape)
    {slot : Fin s → Fin t} (hinj : Function.Injective slot) (ρ : Fin s → WTape) :
    upd τ (f ∘ slot) ρ ∘ f = upd (τ ∘ f) slot ρ := by
  funext x
  by_cases hx : ∃ i, slot i = x
  · obtain ⟨i, rfl⟩ := hx
    simp only [Function.comp_apply]
    rw [← Function.comp_apply (f := f) (g := slot), upd_slot τ (hf.comp hinj), upd_slot _ hinj]
  · push Not at hx
    simp only [Function.comp_apply]
    rw [upd_other τ (f ∘ slot) ρ (f x) (fun i h => hx i (hf h)), upd_other _ _ _ _ hx]
    rfl

theorem Exec.map (f : Fin t → Fin t') (hf : Function.Injective f) {c : Cmd a t} {σ σ' : Fin t → WTape}
    {k : ℕ} (h : Exec c σ σ' k) :
    ∀ τ : Fin t' → WTape, τ ∘ f = σ → ∃ τ', Exec (c.map f hf) τ τ' k ∧ τ' ∘ f = σ' ∧
      ∀ x, (∀ y, f y ≠ x) → τ' x = τ x := by
  induction h with
  | @prim P slot hinj σ hpre =>
    intro τ hτ
    subst hτ
    refine ⟨upd τ (f ∘ slot) (P.sem (τ ∘ (f ∘ slot))), Exec.prim hpre, upd_comp f hf τ hinj _,
      fun x hx => upd_other _ _ _ _ (fun i => hx (slot i))⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    intro τ hτ
    obtain ⟨τ₁, e₁, c₁, o₁⟩ := ih₁ τ hτ
    obtain ⟨τ₂, e₂, c₂, o₂⟩ := ih₂ τ₁ c₁
    exact ⟨τ₂, .seq e₁ e₂, c₂, fun x hx => (o₂ x hx).trans (o₁ x hx)⟩
  | @loop_done i b σ hnil =>
    intro τ hτ
    subst hτ
    exact ⟨τ, .loop_done hnil, rfl, fun _ _ => rfl⟩
  | @loop_step i b σ σ₁ σ₂ k₁ k₂ hne h₁ h₂ ih₁ ih₂ =>
    intro τ hτ
    subst hτ
    obtain ⟨τ₁, e₁, c₁, o₁⟩ := ih₁ τ rfl
    obtain ⟨τ₂, e₂, c₂, o₂⟩ := ih₂ τ₁ c₁
    exact ⟨τ₂, .loop_step hne e₁ e₂, c₂, fun x hx => (o₂ x hx).trans (o₁ x hx)⟩
  | @cond_true i c d σ σ' k hc h₁ ih =>
    intro τ hτ
    subst hτ
    obtain ⟨τ', e, c', o⟩ := ih τ rfl
    exact ⟨τ', .cond_true hc e, c', o⟩
  | @cond_false i c d σ σ' k hc h₁ ih =>
    intro τ hτ
    subst hτ
    obtain ⟨τ', e, c', o⟩ := ih τ rfl
    exact ⟨τ', .cond_false hc e, c', o⟩

theorem Runs.map (f : Fin t → Fin t') (hf : Function.Injective f) {c : Cmd a t} {σ : Fin t → WTape}
    {Q : (Fin t → WTape) → Prop} {B : ℕ} (h : Runs c σ Q B) (τ : Fin t' → WTape) (hτ : τ ∘ f = σ) :
    Runs (c.map f hf) τ (fun τ' => Q (τ' ∘ f) ∧ ∀ x, (∀ y, f y ≠ x) → τ' x = τ x) B := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  obtain ⟨τ', e, c', o⟩ := he.map f hf τ hτ
  exact ⟨τ', k, e, ⟨c' ▸ hq, o⟩, hk⟩

end IntegerMultBounds.Schoenhage

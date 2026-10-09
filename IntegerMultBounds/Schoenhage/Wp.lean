import IntegerMultBounds.Schoenhage.Ops

/-! Weakest preconditions for word programs. `WP c σ Q` unfolds a program
symbolically: a primitive demands its precondition and passes its exact
effect and cost on, sequencing threads states and adds the connecting step,
a branch splits on its test, and a loop asks for an execution. `wp_sound`
turns a weakest precondition into an execution, so straight-line correctness
proofs become simplification of the unfolded conditions. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-- The weakest precondition of `c` for the postcondition `Q` on state and cost. -/
def WP : Cmd a t → (Fin t → WTape) → ((Fin t → WTape) → ℕ → Prop) → Prop
  | .prim P slot _, σ, Q => P.pre (σ ∘ slot) ∧ Q (upd σ slot (P.sem (σ ∘ slot))) (P.cost (σ ∘ slot))
  | .seq c d, σ, Q => WP c σ (fun σ₁ k₁ => WP d σ₁ (fun σ₂ k₂ => Q σ₂ (k₁ + 1 + k₂)))
  | .cond i c d, σ, Q => (StartsOne (σ i) → WP c σ (fun σ' k => Q σ' (k + 1))) ∧
      (¬ StartsOne (σ i) → WP d σ (fun σ' k => Q σ' (k + 1)))
  | .loop i b, σ, Q => ∃ σ' k, Exec (.loop i b) σ σ' k ∧ Q σ' k

theorem wp_sound : ∀ (c : Cmd a t) (σ : Fin t → WTape) (Q : (Fin t → WTape) → ℕ → Prop),
    WP c σ Q → ∃ σ' k, Exec c σ σ' k ∧ Q σ' k
  | .prim P slot hinj, σ, Q, ⟨hp, hq⟩ => ⟨_, _, .prim hp, hq⟩
  | .seq c d, σ, Q, h => by
    obtain ⟨σ₁, k₁, h₁, hw⟩ := wp_sound c σ _ h
    obtain ⟨σ₂, k₂, h₂, hq⟩ := wp_sound d σ₁ _ hw
    exact ⟨σ₂, _, .seq h₁ h₂, hq⟩
  | .cond i c d, σ, Q, ⟨ht, hf⟩ => by
    by_cases hs : StartsOne (σ i)
    · obtain ⟨σ', k, he, hq⟩ := wp_sound c σ _ (ht hs)
      exact ⟨σ', _, .cond_true hs he, hq⟩
    · obtain ⟨σ', k, he, hq⟩ := wp_sound d σ _ (hf hs)
      exact ⟨σ', _, .cond_false hs he, hq⟩
  | .loop i b, σ, Q, h => h

theorem wp_mono : ∀ (c : Cmd a t) (σ : Fin t → WTape) (Q Q' : (Fin t → WTape) → ℕ → Prop),
    (∀ σ' k, Q σ' k → Q' σ' k) → WP c σ Q → WP c σ Q'
  | .prim P slot hinj, σ, Q, Q', hQ, ⟨hp, hq⟩ => ⟨hp, hQ _ _ hq⟩
  | .seq c d, σ, Q, Q', hQ, h =>
    wp_mono c σ _ _ (fun σ₁ k₁ h₁ => wp_mono d σ₁ _ _ (fun σ₂ k₂ h₂ => hQ _ _ h₂) h₁) h
  | .cond i c d, σ, Q, Q', hQ, ⟨ht, hf⟩ =>
    ⟨fun hs => wp_mono c σ _ _ (fun _ _ h => hQ _ _ h) (ht hs),
     fun hs => wp_mono d σ _ _ (fun _ _ h => hQ _ _ h) (hf hs)⟩
  | .loop i b, σ, Q, Q', hQ, ⟨σ', k, he, hq⟩ => ⟨σ', k, he, hQ _ _ hq⟩

/-- A weakest precondition with a bounded cost gives `Runs`. -/
theorem Runs.of_wp {c : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B : ℕ}
    (h : WP c σ (fun σ' k => Q σ' ∧ k ≤ B)) : Runs c σ Q B := by
  obtain ⟨σ', k, he, hq, hk⟩ := wp_sound c σ _ h
  exact ⟨σ', k, he, hq, hk⟩

/-- Executions are deterministic enough for weakest preconditions: an
execution reaching a state satisfying `Q` establishes the weakest precondition. -/
theorem wp_of_exec {c : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ} (h : Exec c σ σ' k) :
    ∀ {Q : (Fin t → WTape) → ℕ → Prop}, Q σ' k → WP c σ Q := by
  induction h with
  | prim hp => intro Q hq; exact ⟨hp, hq⟩
  | seq h₁ h₂ ih₁ ih₂ => intro Q hq; exact ih₁ (ih₂ hq)
  | loop_done hi => intro Q hq; exact ⟨_, _, .loop_done hi, hq⟩
  | loop_step hi h₁ h₂ _ _ => intro Q hq; exact ⟨_, _, .loop_step hi h₁ h₂, hq⟩
  | cond_true hc h₁ ih => intro Q hq; exact ⟨fun _ => ih hq, fun hn => absurd hc hn⟩
  | cond_false hc h₁ ih => intro Q hq; exact ⟨fun hn => absurd hn hc, fun _ => ih hq⟩

/-- A proved fragment inside a weakest precondition. -/
theorem wp_of_runs {c : Cmd a t} {σ : Fin t → WTape} {P : (Fin t → WTape) → Prop} {B : ℕ}
    {Q : (Fin t → WTape) → ℕ → Prop} (h : Runs c σ P B) (hQ : ∀ σ' k, P σ' → k ≤ B → Q σ' k) :
    WP c σ Q := by
  obtain ⟨σ', k, he, hp, hk⟩ := h
  exact wp_of_exec he (hQ σ' k hp hk)

/-! ### Primitive rules -/

theorem wp_rewind (i : Fin t) (σ : Fin t → WTape) (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (rewind i) σ Q ↔
      Q (Function.update σ i ⟨[], (σ i).left.reverse ++ (σ i).right⟩) (clen (σ i).left + 2) := by
  simp only [rewind, WP, upd_one]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

theorem wp_back (i : Fin t) (σ : Fin t → WTape) (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (back i) σ Q ↔ (σ i).left ≠ [] ∧
      Q (Function.update σ i ⟨(σ i).left.tail, (σ i).left.headD [] :: (σ i).right⟩)
        (((σ i).left.headD []).length + 3) := by
  simp only [back, WP, upd_one]
  rfl

theorem wp_clear (i : Fin t) (σ : Fin t → WTape) (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (clear i) σ Q ↔ Q (Function.update σ i ⟨[], []⟩) (2 * clen (σ i).words + 2) := by
  simp only [clear, WP, upd_one]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

theorem wp_emit (ws : List (List Bool)) (i : Fin t) (σ : Fin t → WTape)
    (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (emit ws i) σ Q ↔ (σ i).right = [] ∧
      Q (Function.update σ i ⟨ws.reverse ++ (σ i).left, []⟩) (clen ws) := by
  simp only [emit, WP, upd_one]
  rfl

theorem wp_op0 (R : Rule 0) (ext : Bool) {d o : Fin t} (h : d ≠ o) (σ : Fin t → WTape)
    (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (op0 R ext d o h) σ Q ↔
      ((σ d).right ≠ [] ∧ (σ o).right = [] ∧
        syms (parse (output R (σ d).cur (fun j => j.elim0))) = output R (σ d).cur (fun j => j.elim0) ∧
        (ext = true → (σ o).left ≠ [] ∧ parse (output R (σ d).cur (fun j => j.elim0)) ≠ [])) ∧
      Q (Function.update (Function.update σ d (σ d).next) o
          ((σ o).put ext (parse (output R (σ d).cur (fun j => j.elim0)))))
        (time R (σ d).cur (fun j => j.elim0)) := by
  have sd : slot0 d o drv = d := by simp [slot0, drv]
  have so : slot0 d o out = o := by simp [slot0, out]
  have hz : (fun j : Fin 0 => (σ (slot0 d o (oth j))).cur) = fun j => j.elim0 :=
    funext fun j => j.elim0
  simp only [op0, WP, upd_slot0 σ h]
  have e1 : streamSem R ext (σ ∘ slot0 d o) drv = (σ d).next := by
    rw [streamSem]; simp only [drv_ne_out, ↓reduceIte]; simp [sd]
  have e2 : streamSem R ext (σ ∘ slot0 d o) out =
      (σ o).put ext (parse (output R (σ d).cur (fun j => j.elim0))) := by
    simp only [streamSem, ↓reduceIte, Function.comp_apply, so, sd, hz]
  have ec : (time R ((σ ∘ slot0 d o) drv).cur fun j => ((σ ∘ slot0 d o) (oth j)).cur) =
      time R (σ d).cur (fun j => j.elim0) := by
    simp only [Function.comp_apply, sd, hz]
  rw [e1, e2, ec]
  apply and_congr_left'
  simp only [StreamPre, Function.comp_apply, sd, so, hz]
  constructor
  · rintro ⟨h1, -, h3, vs, h4, h5⟩
    refine ⟨h1, h3, by rw [h4, parse_syms], fun he => ?_⟩
    rw [h4, parse_syms]; exact h5 he
  · rintro ⟨h1, h3, h4, h5⟩
    exact ⟨h1, fun j => j.elim0, h3, _, h4.symm, h5⟩

theorem wp_op1 (R : Rule 1) (ext : Bool) {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o)
    (σ : Fin t → WTape) (Q : (Fin t → WTape) → ℕ → Prop) :
    WP (a := a) (op1 R ext d e o h1 h2 h3) σ Q ↔
      ((σ d).right ≠ [] ∧ (σ e).right ≠ [] ∧ (σ o).right = [] ∧
        syms (parse (output R (σ d).cur (fun _ => (σ e).cur))) = output R (σ d).cur (fun _ => (σ e).cur) ∧
        (ext = true → (σ o).left ≠ [] ∧ parse (output R (σ d).cur (fun _ => (σ e).cur)) ≠ [])) ∧
      Q (Function.update (Function.update (Function.update σ d (σ d).next) e (σ e).next) o
          ((σ o).put ext (parse (output R (σ d).cur (fun _ => (σ e).cur)))))
        (time R (σ d).cur (fun _ => (σ e).cur)) := by
  have sd : slot1 d e o drv = d := by simp [slot1, drv]
  have se : ∀ j, slot1 d e o (oth j) = e := fun j => by have := j.isLt; simp [slot1, oth]
  have so : slot1 d e o out = o := by simp [slot1, out]
  have hz : (fun j : Fin 1 => (σ (slot1 d e o (oth j))).cur) = fun _ => (σ e).cur :=
    funext fun j => by rw [se]
  simp only [op1, WP, upd_slot1 σ h1 h2 h3]
  have e1 : streamSem R ext (σ ∘ slot1 d e o) drv = (σ d).next := by
    rw [streamSem]; simp only [drv_ne_out, ↓reduceIte]; simp [sd]
  have e2 : streamSem R ext (σ ∘ slot1 d e o) (oth 0) = (σ e).next := by
    rw [streamSem]; simp only [oth_ne_out, ↓reduceIte]; simp [se]
  have e3 : streamSem R ext (σ ∘ slot1 d e o) out =
      (σ o).put ext (parse (output R (σ d).cur (fun _ => (σ e).cur))) := by
    simp only [streamSem, ↓reduceIte, Function.comp_apply, so, sd, hz]
  have ec : (time R ((σ ∘ slot1 d e o) drv).cur fun j => ((σ ∘ slot1 d e o) (oth j)).cur) =
      time R (σ d).cur (fun _ => (σ e).cur) := by
    simp only [Function.comp_apply, sd, hz]
  rw [e1, e2, e3, ec]
  apply and_congr_left'
  simp only [StreamPre, Function.comp_apply, sd, so, se, hz]
  constructor
  · rintro ⟨h1, h2, h3, vs, h4, h5⟩
    refine ⟨h1, h2 0, h3, by rw [h4, parse_syms], fun he => ?_⟩
    rw [h4, parse_syms]; exact h5 he
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, fun _ => h2, h3, _, h4.symm, h5⟩

end IntegerMultBounds.Schoenhage

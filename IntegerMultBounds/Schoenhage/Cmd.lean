import IntegerMultBounds.Schoenhage.FMachine
import IntegerMultBounds.Schoenhage.Words
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.PlacementBank

/-! Word programs: a small language over banks of word tapes, compiled to
literal programs. A primitive is a verified machine on a few tapes with an
abstract effect on their word zippers; programs place primitives on chosen
tapes, sequence them, loop while a tape has a word under its head, and branch
on whether the current word starts with a one bit. `compile_correct`: every
big-step execution of a program is a run of the compiled machine from the
encoded bank to the encoded result, within the execution's cost. -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

/-- The physical bank of a bank of word tapes. -/
def enc (σ : Fin t → WTape) : Tapes t a := ⟨fun x => (σ x).pos, fun x => (σ x).tape⟩

/-- A verified primitive on `s` word tapes. -/
structure Prim (a : ℕ) where
  s : ℕ
  hs : 0 < s
  M : FMachine s a
  pre : (Fin s → WTape) → Prop
  sem : (Fin s → WTape) → (Fin s → WTape)
  cost : (Fin s → WTape) → ℕ
  spec : ∀ σ, pre σ → HoareTime (M.toProgram hs) (· = enc σ) (· = enc (sem σ)) (cost σ)

/-- Word programs over `t` tapes. -/
inductive Cmd (a t : ℕ) : Type 1 where
  | prim (P : Prim a) (slot : Fin P.s → Fin t) (hinj : Function.Injective slot)
  | seq (c d : Cmd a t)
  | loop (i : Fin t) (body : Cmd a t)
  | cond (i : Fin t) (c d : Cmd a t)

/-- Replace the slotted tapes. -/
noncomputable def upd {s : ℕ} (σ : Fin t → WTape) (slot : Fin s → Fin t) (τ : Fin s → WTape) :
    Fin t → WTape :=
  fun x => if h : ∃ i, slot i = x then τ h.choose else σ x

theorem upd_slot {s : ℕ} (σ : Fin t → WTape) {slot : Fin s → Fin t} (hinj : Function.Injective slot)
    (τ : Fin s → WTape) (i : Fin s) : upd σ slot τ (slot i) = τ i := by
  have h : ∃ j, slot j = slot i := ⟨i, rfl⟩
  simp only [upd, h, ↓reduceDIte]
  rw [hinj h.choose_spec]

theorem upd_other {s : ℕ} (σ : Fin t → WTape) (slot : Fin s → Fin t) (τ : Fin s → WTape) (x : Fin t)
    (hx : ∀ i, slot i ≠ x) : upd σ slot τ x = σ x := by
  have h : ¬ ∃ i, slot i = x := fun ⟨i, hi⟩ => hx i hi
  simp [upd, h]

/-- The loop test: the head is on a word. -/
def onWord (i : Fin t) (syms : Fin t → Fin (a + 4)) : Bool := decide (syms i ≠ blank)

/-- The branch test: the current word starts with a one. -/
def onOne (i : Fin t) (syms : Fin t → Fin (a + 4)) : Bool := decide (syms i = bitSymbol true)

theorem le_of_slot {s : ℕ} {slot : Fin s → Fin t} (hinj : Function.Injective slot) : s ≤ t := by
  simpa using Fintype.card_le_of_injective slot hinj

/-- The compiled program. -/
noncomputable def compile (ht : 0 < t) : Cmd a t → (q : ℕ) × Program t q a
  | .prim P slot hinj => ⟨_, Placement.placed (P.M.toProgram P.hs)
      (InjectivePlacement.placement slot hinj (u := t - P.s) (by have := le_of_slot hinj; omega))⟩
  | .seq c d => ⟨_, Machine.seq (compile ht c).2 (compile ht d).2⟩
  | .loop i b => ⟨_, whileLoop (compile ht b).2 (onWord i)⟩
  | .cond i c d => ⟨_, branch (onOne i) (compile ht c).2 (compile ht d).2⟩

/-- The branch condition on word tapes. -/
def StartsOne (T : WTape) : Prop := ∃ w R, T.right = (true :: w) :: R

/-- Big-step executions with their costs. -/
inductive Exec : Cmd a t → (Fin t → WTape) → (Fin t → WTape) → ℕ → Prop where
  | prim {P : Prim a} {slot : Fin P.s → Fin t} {hinj : Function.Injective slot} {σ : Fin t → WTape}
      (h : P.pre (σ ∘ slot)) :
      Exec (.prim P slot hinj) σ (upd σ slot (P.sem (σ ∘ slot))) (P.cost (σ ∘ slot))
  | seq {c d : Cmd a t} {σ σ₁ σ₂ : Fin t → WTape} {k₁ k₂ : ℕ}
      (h₁ : Exec c σ σ₁ k₁) (h₂ : Exec d σ₁ σ₂ k₂) : Exec (.seq c d) σ σ₂ (k₁ + 1 + k₂)
  | loop_done {i : Fin t} {b : Cmd a t} {σ : Fin t → WTape} (h : (σ i).right = []) :
      Exec (.loop i b) σ σ 0
  | loop_step {i : Fin t} {b : Cmd a t} {σ σ₁ σ₂ : Fin t → WTape} {k₁ k₂ : ℕ}
      (h : (σ i).right ≠ []) (h₁ : Exec b σ σ₁ k₁) (h₂ : Exec (.loop i b) σ₁ σ₂ k₂) :
      Exec (.loop i b) σ σ₂ (k₁ + 2 + k₂)
  | cond_true {i : Fin t} {c d : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ}
      (h : StartsOne (σ i)) (h₁ : Exec c σ σ' k) : Exec (.cond i c d) σ σ' (k + 1)
  | cond_false {i : Fin t} {c d : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ}
      (h : ¬ StartsOne (σ i)) (h₁ : Exec d σ σ' k) : Exec (.cond i c d) σ σ' (k + 1)

theorem reads_enc (σ : Fin t → WTape) (i : Fin t) :
    (enc (a := a) σ).reads i = ((syms (σ i).right)[0]?.map sym).getD blank := by
  have := (σ i).tape_at_pos (a := a) 0
  simpa [Tapes.reads, enc] using this

theorem onWord_enc (σ : Fin t → WTape) (i : Fin t) :
    onWord i (enc (a := a) σ).reads = decide ((σ i).right ≠ []) := by
  unfold onWord
  rw [reads_enc]
  rcases h : (σ i).right with _ | ⟨w, R⟩
  · simp [syms_cons]
  · rcases w with _ | ⟨b, w⟩
    · simp [syms_cons, sym, separator, blank]
    · simp only [syms_cons, List.map_cons, List.cons_append, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true, decide_true,
        decide_eq_true_eq]
      exact sym_ne_blank _

theorem onOne_enc_true (σ : Fin t → WTape) (i : Fin t) (h : StartsOne (σ i)) :
    onOne i (enc (a := a) σ).reads = true := by
  obtain ⟨w, R, hr⟩ := h
  unfold onOne
  rw [reads_enc, hr]
  simp [syms_cons, sym]

theorem onOne_enc_false (σ : Fin t → WTape) (i : Fin t) (h : ¬ StartsOne (σ i)) :
    onOne i (enc (a := a) σ).reads = false := by
  unfold onOne StartsOne at *
  rw [reads_enc]
  rcases hr : (σ i).right with _ | ⟨w, R⟩
  · simp [syms_cons, bitSymbol, blank, Fin.ext_iff]
  · rcases w with _ | ⟨b, w⟩
    · simp [syms_cons, sym, separator, bitSymbol, Fin.ext_iff]
    · cases b
      · simp [syms_cons, sym, bitSymbol, Fin.ext_iff]
      · exact absurd ⟨w, R, hr⟩ h

/-- Every execution is a run of the compiled machine within its cost. -/
theorem compile_correct (ht : 0 < t) {c : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ}
    (h : Exec c σ σ' k) :
    HoareTime (compile ht c).2 (· = enc σ) (· = enc σ') k := by
  induction h with
  | @prim P slot hinj σ hpre =>
    have hsize : P.s + (t - P.s) = t := by have := le_of_slot hinj; omega
    refine InjectivePlacement.hoare_exact (P.spec _ hpre) slot hinj hsize (enc σ) _ ?_ ?_
    · rw [InjectivePlacement.active_bank]; rfl
    · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
      · by_cases hx : ∃ i, slot i = x
        · obtain ⟨i, rfl⟩ := hx
          rw [InjectivePlacement.replace_head_slot]
          simp [enc, upd_slot σ hinj]
        · push Not at hx
          rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ hx]
          simp [enc, upd_other σ slot _ x hx]
      · by_cases hx : ∃ i, slot i = x
        · obtain ⟨i, rfl⟩ := hx
          rw [InjectivePlacement.replace_tape_slot]
          simp [enc, upd_slot σ hinj]
        · push Not at hx
          rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hx]
          simp [enc, upd_other σ slot _ x hx]
  | seq h₁ h₂ ih₁ ih₂ => exact ih₁.seq ih₂
  | @loop_done i b σ hnil =>
    show HoareTime (whileLoop (compile ht b).2 (onWord i)) _ _ _
    intro v hv
    subst hv
    refine ⟨0, (enc σ).start _, le_rfl, rfl, ?_, rfl⟩
    apply while_step_exit
    rw [onWord_enc]; simp [hnil]
  | @loop_step i b σ σ₁ σ₂ k₁ k₂ hne h₁ h₂ ih₁ ih₂ =>
    change HoareTime (whileLoop (compile ht b).2 (onWord i)) _ _ _ at ih₂ ⊢
    intro v hv
    subst hv
    obtain ⟨n, c, hn, hr, hh, hp⟩ := ih₁ (enc σ) rfl
    obtain ⟨m, d, hm, hs, hd, hq⟩ := ih₂ c.tapes hp
    refine ⟨n + 2 + m, d, by omega, ?_, hd, hq⟩
    rw [run_add, while_run_iteration (compile ht b).2 (onWord i) (enc σ) (by rw [onWord_enc]; simpa using hne) hr hh]
    exact hs
  | @cond_true i c d σ σ' k hc h₁ ih =>
    show HoareTime (branch (onOne i) (compile ht c).2 (compile ht d).2) _ _ _
    have := branch_hoare (onOne i) (pre := (· = enc σ)) (post := (· = enc σ'))
      (M := (compile ht c).2) (N := (compile ht d).2) (bM := k) (bN := 0)
      (fun v ⟨hv, _⟩ => ih v hv)
      (fun v ⟨hv, hf⟩ => absurd hf (by subst hv; rw [onOne_enc_true σ i hc]; simp))
    simpa using this
  | @cond_false i c d σ σ' k hc h₁ ih =>
    show HoareTime (branch (onOne i) (compile ht c).2 (compile ht d).2) _ _ _
    have := branch_hoare (onOne i) (pre := (· = enc σ)) (post := (· = enc σ'))
      (M := (compile ht c).2) (N := (compile ht d).2) (bM := 0) (bN := k)
      (fun v ⟨hv, htr⟩ => absurd htr (by subst hv; rw [onOne_enc_false σ i hc]; simp))
      (fun v ⟨hv, _⟩ => ih v hv)
    simpa using this

end IntegerMultBounds.Schoenhage

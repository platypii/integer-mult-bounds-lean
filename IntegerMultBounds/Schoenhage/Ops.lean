import IntegerMultBounds.Schoenhage.StreamPrim
import IntegerMultBounds.Schoenhage.Moves
import IntegerMultBounds.Schoenhage.Rules

/-! Word-program building blocks on named tapes, with execution lemmas in a
pre/post style: `Runs c σ Q B` says `c` executes from `σ` to a bank
satisfying `Q` within `B` steps. Streaming rules with zero, one or two extra
inputs, and the rewind, back, clear and emit primitives, each have an exact
effect stated with `Function.update`. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a t : ℕ}

/-- A register holding `w`. -/
def reg (w : List Bool) : WTape := ⟨[], [w]⟩

/-- An empty tape. -/
def emp : WTape := ⟨[], []⟩

@[simp] theorem reg_cur (w : List Bool) : (reg w).cur = w := rfl
@[simp] theorem reg_right (w : List Bool) : (reg w).right = [w] := rfl
@[simp] theorem reg_left (w : List Bool) : (reg w).left = [] := rfl
@[simp] theorem reg_next (w : List Bool) : (reg w).next = ⟨[w], []⟩ := rfl
@[simp] theorem emp_right : emp.right = [] := rfl
@[simp] theorem emp_left : emp.left = [] := rfl
@[simp] theorem WTape.next_mk (L R : List (List Bool)) :
    (⟨L, R⟩ : WTape).next = ⟨R.headD [] :: L, R.tail⟩ := rfl
@[simp] theorem WTape.cur_mk (L R : List (List Bool)) : (⟨L, R⟩ : WTape).cur = R.headD [] := rfl
@[simp] theorem WTape.put_true_cons (u : List Bool) (L : List (List Bool)) (v : List Bool)
    (vs : List (List Bool)) : (⟨u :: L, []⟩ : WTape).put true (v :: vs) = ⟨vs.reverse ++ (u ++ v) :: L, []⟩ :=
  rfl

@[simp] theorem WTape.put_false (L : List (List Bool)) (vs : List (List Bool)) :
    (⟨L, []⟩ : WTape).put false vs = ⟨vs.reverse ++ L, []⟩ := by
  cases L <;> rfl

/-- `c` runs from `σ` into `Q` within `B` steps. -/
def Runs (c : Cmd a t) (σ : Fin t → WTape) (Q : (Fin t → WTape) → Prop) (B : ℕ) : Prop :=
  ∃ σ' k, Exec c σ σ' k ∧ Q σ' ∧ k ≤ B

theorem Runs.mono {c : Cmd a t} {σ} {Q Q' : (Fin t → WTape) → Prop} {B B' : ℕ}
    (h : Runs c σ Q B) (hQ : ∀ σ', Q σ' → Q' σ') (hB : B ≤ B') : Runs c σ Q' B' := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  exact ⟨σ', k, he, hQ σ' hq, hk.trans hB⟩

theorem Runs.seq {c d : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B₁ B₂ : ℕ}
    (h : Runs c σ (fun σ₁ => Runs d σ₁ Q B₂) B₁) : Runs (.seq c d) σ Q (B₁ + 1 + B₂) := by
  obtain ⟨σ₁, k₁, h₁, ⟨σ₂, k₂, h₂, hq, hk₂⟩, hk₁⟩ := h
  exact ⟨σ₂, k₁ + 1 + k₂, .seq h₁ h₂, hq, by omega⟩

/-- Chain an exact step into the rest of a program. -/
theorem Runs.then {c d : Cmd a t} {σ σ₁ : Fin t → WTape} {Q : (Fin t → WTape) → Prop} {B₁ B₂ : ℕ}
    (h₁ : Runs c σ (· = σ₁) B₁) (h₂ : Runs d σ₁ Q B₂) : Runs (.seq c d) σ Q (B₁ + 1 + B₂) :=
  Runs.seq (h₁.mono (fun _ h => h ▸ h₂) le_rfl)

/-- Weaken the bound. -/
theorem Runs.le {c : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B B' : ℕ}
    (h : Runs c σ Q B) (hB : B ≤ B') : Runs c σ Q B' := h.mono (fun _ h => h) hB

theorem Runs.cond_true {i : Fin t} {c d : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B : ℕ}
    (hc : StartsOne (σ i)) (h : Runs c σ Q B) : Runs (.cond i c d) σ Q (B + 1) := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  exact ⟨σ', k + 1, .cond_true hc he, hq, by omega⟩

theorem Runs.cond_false {i : Fin t} {c d : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B : ℕ}
    (hc : ¬ StartsOne (σ i)) (h : Runs d σ Q B) : Runs (.cond i c d) σ Q (B + 1) := by
  obtain ⟨σ', k, he, hq, hk⟩ := h
  exact ⟨σ', k + 1, .cond_false hc he, hq, by omega⟩

theorem Runs.loop_done {i : Fin t} {b : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop}
    (hi : (σ i).right = []) (hq : Q σ) : Runs (.loop i b) σ Q 0 :=
  ⟨σ, 0, .loop_done hi, hq, le_rfl⟩

theorem Runs.loop_step {i : Fin t} {b : Cmd a t} {σ} {Q : (Fin t → WTape) → Prop} {B₁ B₂ : ℕ}
    (hi : (σ i).right ≠ []) (h : Runs b σ (fun σ₁ => Runs (.loop i b) σ₁ Q B₂) B₁) :
    Runs (.loop i b) σ Q (B₁ + 2 + B₂) := by
  obtain ⟨σ₁, k₁, h₁, ⟨σ₂, k₂, h₂, hq, hk₂⟩, hk₁⟩ := h
  exact ⟨σ₂, k₁ + 2 + k₂, .loop_step hi h₁ h₂, hq, by omega⟩

/-- A loop whose body consumes one word of the loop tape: an invariant indexed
by the number of remaining words, with a per-iteration bound. -/
theorem Runs.loop_count {i : Fin t} {b : Cmd a t} (I : ℕ → (Fin t → WTape) → Prop) (C : ℕ)
    (hdone : ∀ σ, I 0 σ → (σ i).right = [])
    (hstep : ∀ n σ, I (n + 1) σ → (σ i).right ≠ [] ∧ Runs b σ (I n) C) :
    ∀ n σ, I n σ → Runs (.loop i b) σ (I 0) (n * (C + 2)) := by
  intro n
  induction n with
  | zero => intro σ h; exact (Runs.loop_done (b := b) (hdone σ h) h).mono (fun _ h => h) (by simp)
  | succ n ih =>
    intro σ h
    obtain ⟨hne, hb⟩ := hstep n σ h
    have := Runs.loop_step (B₂ := n * (C + 2)) hne (hb.mono (fun σ₁ h₁ => ih σ₁ h₁) le_rfl)
    exact this.mono (fun _ h => h) (by rw [Nat.succ_mul]; omega)

/-! ### Slots -/

/-- Slots for a stream with one extra input. -/
def slot1 (d e o : Fin t) : Fin (1 + 2) → Fin t := fun i =>
  if i.val = 0 then d else if i.val = 1 then e else o

theorem slot1_inj {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) :
    Function.Injective (slot1 d e o) := by
  intro i j h
  simp only [slot1] at h
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at h <;> omega

/-- Slots for a stream with no extra input. -/
def slot0 (d o : Fin t) : Fin (0 + 2) → Fin t := fun i => if i.val = 0 then d else o

theorem slot0_inj {d o : Fin t} (h : d ≠ o) : Function.Injective (slot0 d o) := by
  intro i j hij
  simp only [slot0] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> omega

/-- Slots for a stream with two extra inputs. -/
def slot2 (d e f o : Fin t) : Fin (2 + 2) → Fin t := fun i =>
  if i.val = 0 then d else if i.val = 1 then e else if i.val = 2 then f else o

theorem slot2_inj {d e f o : Fin t} (h1 : d ≠ e) (h2 : d ≠ f) (h3 : d ≠ o) (h4 : e ≠ f)
    (h5 : e ≠ o) (h6 : f ≠ o) : Function.Injective (slot2 d e f o) := by
  intro i j hij
  simp only [slot2] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> omega

/-- A one-tape slot. -/
def slotOne (i : Fin t) : Fin 1 → Fin t := fun _ => i

theorem slotOne_inj (i : Fin t) : Function.Injective (slotOne i) := by
  intro x y _; exact Subsingleton.elim x y

/-! ### Commands -/

/-- Stream with no extra input from `d` to `o`. -/
noncomputable def op0 (R : Rule 0) (ext : Bool) (d o : Fin t) (h : d ≠ o) : Cmd a t :=
  .prim (streamPrim R ext) (slot0 d o) (slot0_inj h)

/-- Stream with one extra input. -/
noncomputable def op1 (R : Rule 1) (ext : Bool) (d e o : Fin t) (h1 : d ≠ e) (h2 : d ≠ o)
    (h3 : e ≠ o) : Cmd a t :=
  .prim (streamPrim R ext) (slot1 d e o) (slot1_inj h1 h2 h3)

/-- Stream with two extra inputs. -/
noncomputable def op2 (R : Rule 2) (ext : Bool) (d e f o : Fin t) (h1 : d ≠ e) (h2 : d ≠ f)
    (h3 : d ≠ o) (h4 : e ≠ f) (h5 : e ≠ o) (h6 : f ≠ o) : Cmd a t :=
  .prim (streamPrim R ext) (slot2 d e f o) (slot2_inj h1 h2 h3 h4 h5 h6)

noncomputable def rewind (i : Fin t) : Cmd a t := .prim Rewind.prim (slotOne i) (slotOne_inj i)
noncomputable def back (i : Fin t) : Cmd a t := .prim Back.prim (slotOne i) (slotOne_inj i)
noncomputable def clear (i : Fin t) : Cmd a t := .prim Clear.prim (slotOne i) (slotOne_inj i)
noncomputable def emit (ws : List (List Bool)) (i : Fin t) : Cmd a t :=
  .prim (Emit.prim ws) (slotOne i) (slotOne_inj i)

/-! ### Effects -/

theorem upd_one (σ : Fin t → WTape) (i : Fin t) (τ : Fin 1 → WTape) :
    upd σ (slotOne i) τ = Function.update σ i (τ 0) := by
  funext x
  by_cases hx : x = i
  · subst hx; rw [Function.update_self]; exact upd_slot σ (slotOne_inj x) τ 0
  · rw [Function.update_of_ne hx, upd_other σ (slotOne i) τ x (fun _ h => hx h.symm)]

theorem runs_rewind (i : Fin t) (σ : Fin t → WTape) :
    Runs (a := a) (rewind i) σ (· = Function.update σ i ⟨[], (σ i).left.reverse ++ (σ i).right⟩)
      (clen (σ i).left + 2) := by
  refine ⟨_, _, Exec.prim (P := Rewind.prim) trivial, ?_, le_rfl⟩
  rw [upd_one]; rfl

theorem runs_back (i : Fin t) (σ : Fin t → WTape) (h : (σ i).left ≠ []) :
    Runs (a := a) (back i) σ
      (· = Function.update σ i ⟨(σ i).left.tail, (σ i).left.headD [] :: (σ i).right⟩)
      (((σ i).left.headD []).length + 3) := by
  refine ⟨_, _, Exec.prim (P := Back.prim) h, ?_, le_rfl⟩
  rw [upd_one]; rfl

theorem runs_clear (i : Fin t) (σ : Fin t → WTape) :
    Runs (a := a) (clear i) σ (· = Function.update σ i ⟨[], []⟩) (2 * clen (σ i).words + 2) := by
  refine ⟨_, _, Exec.prim (P := Clear.prim) trivial, ?_, le_rfl⟩
  rw [upd_one]

theorem runs_emit (ws : List (List Bool)) (i : Fin t) (σ : Fin t → WTape) (h : (σ i).right = []) :
    Runs (a := a) (emit ws i) σ (· = Function.update σ i ⟨ws.reverse ++ (σ i).left, []⟩) (clen ws) := by
  refine ⟨_, _, Exec.prim (P := Emit.prim ws) h, ?_, le_rfl⟩
  rw [upd_one]; rfl

theorem upd_slot0 (σ : Fin t → WTape) {d o : Fin t} (h : d ≠ o) (τ : Fin (0 + 2) → WTape) :
    upd σ (slot0 d o) τ = Function.update (Function.update σ d (τ drv)) o (τ out) := by
  funext x
  by_cases hxo : x = o
  · subst hxo
    rw [Function.update_self]
    have := upd_slot σ (slot0_inj h) τ out
    rwa [show slot0 d x out = x by simp [slot0, out]] at this
  · rw [Function.update_of_ne hxo]
    by_cases hxd : x = d
    · subst hxd
      rw [Function.update_self]
      have := upd_slot σ (slot0_inj h) τ drv
      rwa [show slot0 x o drv = x by simp [slot0, drv]] at this
    · rw [Function.update_of_ne hxd]
      refine upd_other σ _ τ x (fun i hi => ?_)
      simp only [slot0] at hi; split_ifs at hi <;> simp_all

theorem upd_slot1 (σ : Fin t → WTape) {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o)
    (τ : Fin (1 + 2) → WTape) :
    upd σ (slot1 d e o) τ =
      Function.update (Function.update (Function.update σ d (τ drv)) e (τ (oth 0))) o (τ out) := by
  funext x
  have hi := slot1_inj h1 h2 h3
  by_cases hxo : x = o
  · subst hxo
    rw [Function.update_self]
    have := upd_slot σ hi τ out
    rwa [show slot1 d e x out = x by simp [slot1, out]] at this
  · rw [Function.update_of_ne hxo]
    by_cases hxe : x = e
    · subst hxe
      rw [Function.update_self]
      have := upd_slot σ hi τ (oth 0)
      rwa [show slot1 d x o (oth 0) = x by simp [slot1, oth]] at this
    · rw [Function.update_of_ne hxe]
      by_cases hxd : x = d
      · subst hxd
        rw [Function.update_self]
        have := upd_slot σ hi τ drv
        rwa [show slot1 x e o drv = x by simp [slot1, drv]] at this
      · rw [Function.update_of_ne hxd]
        refine upd_other σ _ τ x (fun i hi => ?_)
        simp only [slot1] at hi; split_ifs at hi <;> simp_all

/-- The effect of a one-input stream. -/
theorem runs_op0 (R : Rule 0) (ext : Bool) {d o : Fin t} (h : d ≠ o) (σ : Fin t → WTape)
    (hd : (σ d).right ≠ []) (ho : (σ o).right = []) (vs : List (List Bool))
    (hvs : output R (σ d).cur (fun j => j.elim0) = syms vs)
    (hext : ext = true → (σ o).left ≠ [] ∧ vs ≠ []) :
    Runs (a := a) (op0 R ext d o h) σ
      (· = Function.update (Function.update σ d (σ d).next) o ((σ o).put ext vs))
      (time R (σ d).cur (fun j => j.elim0)) := by
  have hpre : StreamPre R ext (σ ∘ slot0 d o) := by
    refine ⟨by simpa [slot0, drv] using hd, fun j => j.elim0, by simpa [slot0, out, h.symm] using ho,
      vs, ?_, by simpa [slot0, out] using hext⟩
    convert hvs using 3
    simp [slot0, drv]
  refine ⟨_, _, Exec.prim (P := streamPrim R ext) hpre, ?_, ?_⟩
  · rw [upd_slot0 σ h]
    have e1 : (streamPrim (a := a) R ext).sem (σ ∘ slot0 d o) drv = (σ d).next := by
      show streamSem R ext _ drv = _
      rw [streamSem]; simp only [drv_ne_out, ↓reduceIte]; simp [slot0, drv]
    have e2 : (streamPrim (a := a) R ext).sem (σ ∘ slot0 d o) out = (σ o).put ext vs := by
      show streamSem R ext _ out = _
      simp only [streamSem, ↓reduceIte, Function.comp_apply]
      have hs : slot0 d o out = o := by simp [slot0, out]
      have hd' : slot0 d o drv = d := by simp [slot0, drv]
      rw [hs]; congr 1
      rw [show (fun j => (σ (slot0 d o (oth j))).cur) = fun j => j.elim0 from funext fun j => j.elim0,
        hd', hvs, parse_syms]
    rw [e1, e2]
  · show time R (σ (slot0 d o drv)).cur _ ≤ _
    simp only [slot0, drv, ↓reduceIte]
    exact le_of_eq (by congr 1; funext j; exact j.elim0)

/-- The effect of a two-input stream. -/
theorem runs_op1 (R : Rule 1) (ext : Bool) {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o)
    (σ : Fin t → WTape) (hd : (σ d).right ≠ []) (he : (σ e).right ≠ []) (ho : (σ o).right = [])
    (vs : List (List Bool)) (hvs : output R (σ d).cur (fun _ => (σ e).cur) = syms vs)
    (hext : ext = true → (σ o).left ≠ [] ∧ vs ≠ []) :
    Runs (a := a) (op1 R ext d e o h1 h2 h3) σ
      (· = Function.update (Function.update (Function.update σ d (σ d).next) e (σ e).next) o
        ((σ o).put ext vs))
      (time R (σ d).cur (fun _ => (σ e).cur)) := by
  have sd : slot1 d e o drv = d := by simp [slot1, drv]
  have se : ∀ j, slot1 d e o (oth j) = e := fun j => by
    have := j.isLt; simp [slot1, oth]
  have so : slot1 d e o out = o := by simp [slot1, out]
  have hpre : StreamPre R ext (σ ∘ slot1 d e o) := by
    refine ⟨by simpa [sd] using hd, fun j => by simpa [se] using he, by simpa [so] using ho,
      vs, ?_, by simpa [so] using hext⟩
    simp only [Function.comp_apply, sd, se]; exact hvs
  refine ⟨_, _, Exec.prim (P := streamPrim R ext) hpre, ?_, ?_⟩
  · rw [upd_slot1 σ h1 h2 h3]
    have e1 : (streamPrim (a := a) R ext).sem (σ ∘ slot1 d e o) drv = (σ d).next := by
      show streamSem R ext _ drv = _
      rw [streamSem]; simp only [drv_ne_out, ↓reduceIte]; simp [sd]
    have e2 : (streamPrim (a := a) R ext).sem (σ ∘ slot1 d e o) (oth 0) = (σ e).next := by
      show streamSem R ext _ (oth 0) = _
      rw [streamSem]; simp only [oth_ne_out, ↓reduceIte]; simp [se]
    have e3 : (streamPrim (a := a) R ext).sem (σ ∘ slot1 d e o) out = (σ o).put ext vs := by
      show streamSem R ext _ out = _
      simp only [streamSem, ↓reduceIte, Function.comp_apply, so, sd, se, hvs, parse_syms]
    rw [e1, e2, e3]
  · show time R (σ (slot1 d e o drv)).cur (fun j => (σ (slot1 d e o (oth j))).cur) ≤ _
    simp only [sd, se, le_refl]

end IntegerMultBounds.Schoenhage

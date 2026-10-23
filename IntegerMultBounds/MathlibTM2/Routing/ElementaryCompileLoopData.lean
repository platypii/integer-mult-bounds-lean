module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileCall

/-! Fixed-bank invariant and exact input/output formats of the compiler loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

structure ElementaryCoordinate (n : ℕ) where
  target : Fin n
  source : Fin n
  source_ne : source ≠ target

def ElementaryCoordinate.key {n : ℕ} (c : ElementaryCoordinate n) := (c.target, c.source)

def elementaryCoordinateFrames {A n : ℕ} (L : ℕ) : List (ElementaryCoordinate n) → List (Fin (A + 4))
  | [] => []
  | c :: cs => configurationWords (elementaryPairWords L c.target.val c.source.val) ++ elementaryCoordinateFrames L cs

def elementaryCompileBase (n L Lb rowLength : ℕ) : ℕ :=
  (8 * L + 13) + (elementaryCompilerPrepareBound n L Lb rowLength + 1 +
    (26 * (n + rowLength + Lb + L + 3) + 1)) + (4 * L + 5)

structure ElementaryCompileReady {T A : ℕ} (rg : ElementaryCompilerReg → Fin T)
    (R : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) : Prop where
  width : R (rg (.coordinate .width)) = binSyms L n
  rows : R (rg .rows) = rowBits.map bitSymbol
  block : R (rg .block) = binSyms Lb B
  blank : ∀ r, r ∉ elementaryCompilerInputs → R (rg r) = []
  target0 : R (rg (.coordinate .target)) = []
  source0 : R (rg (.coordinate .source)) = []

/-- Canonical compiler operands; every generated header and scratch word starts empty. -/
def elementaryCompilerInputWords {A : ℕ} (n L Lb B : ℕ) (rowBits : List Bool) :
    ElementaryCompilerReg → List (Fin (A + 4))
  | .coordinate .width => binSyms L n
  | .rows => rowBits.map bitSymbol
  | .block => binSyms Lb B
  | _ => []

noncomputable def elementaryCompilerInputBank {T A : ℕ} (rg : ElementaryCompilerReg → Fin T)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :
    Fin T → List (Fin (A + 4)) :=
  Function.extend rg (elementaryCompilerInputWords n L Lb B rowBits) outside

theorem elementaryCompilerInputBank_ready {T A : ℕ} (rg : ElementaryCompilerReg → Fin T)
    (hrg : Function.Injective rg) (outside : Fin T → List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) :
    ElementaryCompileReady rg (elementaryCompilerInputBank rg outside n L Lb B rowBits) n L Lb B rowBits := by
  have hat (r : ElementaryCompilerReg) : elementaryCompilerInputBank rg outside n L Lb B rowBits (rg r) =
      elementaryCompilerInputWords n L Lb B rowBits r := hrg.extend_apply _ _ r
  refine ⟨hat _, hat _, hat _, ?_, hat _, hat _⟩
  intro r hr
  rw [hat]
  cases r with
  | coordinate r =>
    cases r <;> first | rfl | (exfalso; exact hr (by simp [elementaryCompilerInputs]))
  | rows => exact (hr (by simp [elementaryCompilerInputs])).elim
  | block => exact (hr (by simp [elementaryCompilerInputs])).elim
  | header i => rfl
  | mask => rfl
  | output => rfl

theorem elementaryCompilerInputBank_off {T A : ℕ} (rg : ElementaryCompilerReg → Fin T)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool)
    (j : Fin T) (hj : ∀ r, rg r ≠ j) :
    elementaryCompilerInputBank rg outside n L Lb B rowBits j = outside j := by
  apply Function.extend_apply'
  rintro ⟨r, hr⟩
  exact hj r hr

theorem ElementaryCompileReady.congr {T A : ℕ} {rg : ElementaryCompilerReg → Fin T}
    {R R' : Fin T → List (Fin (A + 4))} {n L Lb B : ℕ} {rowBits : List Bool}
    (h : ElementaryCompileReady rg R n L Lb B rowBits)
    (hkeep : ∀ r, r ≠ .output → R' (rg r) = R (rg r)) :
    ElementaryCompileReady rg R' n L Lb B rowBits := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkeep _ (by simp)]; exact h.width
  · rw [hkeep _ (by simp)]; exact h.rows
  · rw [hkeep _ (by simp)]; exact h.block
  · intro r hr
    rw [hkeep r (by intro he; subst r; exact hr (by simp [elementaryCompilerInputs]))]
    exact h.blank r hr
  · rw [hkeep _ (by simp)]; exact h.target0
  · rw [hkeep _ (by simp)]; exact h.source0

/-- A call preserves the loop invariant on every compiler tape except output. -/
theorem elementaryCompileStepBank_keep {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (pair frame rest : List (Fin (A + 4))) (r : ElementaryCompilerReg) (hr : r ≠ .output) :
    elementaryCompileStepBank R rg src saved pair frame rest (rg r) = R (rg r) := by
  simp [elementaryCompileStepBank, Function.update_of_ne (hsrc r).symm,
    Function.update_of_ne (hsaved r).symm, Function.update_of_ne (fun he => hr (hrg he))]

def elementaryCompileLoopBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T)
    (input output : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src []) saved (input.reverse ++ R saved))
    (rg .output) (output ++ R (rg .output))

theorem elementaryFrames_append {n A : ℕ} (ds es : List (ElementaryInstruction n)) :
    elementaryFrames (A := A) (ds ++ es) = elementaryFrames ds ++ elementaryFrames es := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [elementaryFrames, ih, List.append_assoc]

/-- Compiler input remains nonempty until the last complete coordinate pair. -/
theorem elementaryCoordinateFrames_cons_ne_nil {n A : ℕ} (L : ℕ)
    (c : ElementaryCoordinate n) (cs : List (ElementaryCoordinate n)) :
    elementaryCoordinateFrames (A := A) L (c :: cs) ≠ [] := by
  have h := configurationWords_count_le (elementaryPairWords (A := A) L c.target.val c.source.val)
  simp only [elementaryPairWords, List.length_cons, List.length_nil] at h
  intro he
  have hp : configurationWords (elementaryPairWords (A := A) L c.target.val c.source.val) = [] :=
    (List.append_eq_nil_iff.mp he).1
  change 2 ≤ (configurationWords (elementaryPairWords (A := A) L c.target.val c.source.val)).length at h
  rw [hp] at h
  simp at h

/-- Prefix archives and prepended output frames compose in their actual order. -/
theorem elementaryCompileLoopBank_step {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T)
    (hss : src ≠ saved) (hso : src ≠ rg .output) (hao : saved ≠ rg .output)
    (pair frame rest input output : List (Fin (A + 4))) :
    elementaryCompileLoopBank (elementaryCompileStepBank R rg src saved pair frame rest) rg src saved input output =
      elementaryCompileLoopBank R rg src saved (pair ++ input) (output ++ frame) := by
  funext j
  by_cases ho : j = rg .output
  · subst j
    simp [elementaryCompileLoopBank, elementaryCompileStepBank, List.append_assoc]
  · by_cases ha : j = saved
    · subst j
      simp [elementaryCompileLoopBank, elementaryCompileStepBank, hao, List.reverse_append, List.append_assoc]
    · by_cases hs : j = src
      · subst j
        simp [elementaryCompileLoopBank, elementaryCompileStepBank, hss, hso]
      · simp [elementaryCompileLoopBank, elementaryCompileStepBank, ho, ha, hs]

/-- An empty table leaves the entire starting bank unchanged. -/
theorem elementaryCompileLoopBank_nil {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T)
    (hss : src ≠ saved) (hso : src ≠ rg .output) (hao : saved ≠ rg .output) (hsrc : R src = []) :
    elementaryCompileLoopBank R rg src saved [] [] = R := by
  funext j
  by_cases ho : j = rg .output
  · subst j
    simp [elementaryCompileLoopBank]
  · by_cases ha : j = saved
    · subst j
      simp [elementaryCompileLoopBank, hao]
    · by_cases hs : j = src
      · subst j
        simp [elementaryCompileLoopBank, hss, hso, hsrc]
      · simp [elementaryCompileLoopBank, ho, ha, hs]

end IntegerMultBounds.MathlibTM2.Routing

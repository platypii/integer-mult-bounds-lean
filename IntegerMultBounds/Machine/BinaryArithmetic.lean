import IntegerMultBounds.Machine.BinaryPad
import IntegerMultBounds.Machine.BinaryAdd
import IntegerMultBounds.Machine.Frame

/-! Addition of arbitrary-width LSF words by actual padding, physical rewind,
and ripple addition. Both sequential joins are charged as real transitions. -/

namespace IntegerMultBounds.Machine.BinaryArithmetic

variable {a s : ℕ}

def cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (state : Fin s) : Config 3 s a where
  state := state
  head := fun i => if i = 0 then p else if i = 1 then q else r
  tape := fun i => if i = 0 then f else if i = 1 then g else out

@[simp] theorem cfg_mapState {u : ℕ} (f g out : ℤ → Fin (a + 4)) (p q r : ℤ)
    (state : Fin s) (map : Fin s → Fin u) :
    (cfg f g out p q r state).mapState map = cfg f g out p q r (map state) := rfl

/-- First leave the right blank, scan the two equal-width words backwards,
then step off the left blank. The output tape never moves. -/
def rewind (a : ℕ) : Program 3 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols =>
    if state = 2 then none
    else if state = 1 ∧ symbols 0 = blank then
      some (2, fun i => (symbols i, if i = 2 then .stay else .right))
    else some (1, fun i => (symbols i, if i = 2 then .stay else .left))

private theorem rewind_left (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (s : Fin 3)
    (hs : s = 0 ∨ s = 1 ∧ f p ≠ blank) :
    step (rewind a) (cfg f g out p q r s) = some (cfg f g out (p - 1) (q - 1) r 1) := by
  have ht : (rewind a).transition s (fun i => (cfg f g out p q r s).tape i ((cfg f g out p q r s).head i)) =
      some (1, fun i => ((cfg f g out p q r s).tape i ((cfg f g out p q r s).head i),
        if i = 2 then Move.stay else Move.left)) := by
    rcases hs with rfl | ⟨rfl, hp⟩ <;> simp [rewind, cfg, *]
  unfold step
  simp only [cfg] at ht ⊢
  rw [ht]
  dsimp only
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [Move.offset, sub_eq_add_neg]
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

private theorem rewind_right (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (hp : f p = blank) :
    step (rewind a) (cfg f g out p q r 1) = some (cfg f g out (p + 1) (q + 1) r 2) := by
  simp only [step, rewind, cfg, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte, hp, and_self]
  congr 1
  congr 1
  · funext i; fin_cases i <;> simp [Move.offset]
  · funext i j; fin_cases i <;> simp <;> intro hj <;> rw [hj]

private theorem rewind_scan (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) (n : ℕ)
    (hf : ∀ j : ℕ, j < n → f (p - j) ≠ blank) :
    run (rewind a) n (cfg f g out p q r 1) = some (cfg f g out (p - n) (q - n) r 1) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add, ih (fun j hj => hf j (by omega))]
    simp only [Option.bind_some, run_one]
    simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using
      rewind_left f g out (p - n) (q - n) r 1 (Or.inr ⟨rfl, hf n (by omega)⟩)

private theorem word_bit_nonblank (bits : List Bool) (j : ℤ) (hj : 0 ≤ j) (hl : j < bits.length) :
    wordTape (bits.map (bitSymbol (a := a))) j ≠ blank := by
  have hnat : j.toNat < bits.length := by omega
  simp only [wordTape, hj, ↓reduceIte, List.getElem?_map,
    List.getElem?_eq_getElem hnat, Option.map_some, Option.getD_some]
  cases bits[j.toNat] <;> simp [bitSymbol, blank]

/-- Exactly width plus two actual transitions return both operand heads to
zero, preserving both entire operands and an arbitrary stationary third tape. -/
theorem rewind_exact (xs ys : List Bool) (out : ℤ → Fin (a + 4)) (r : ℤ) :
    run (rewind a) (xs.length + 2)
      (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) out xs.length xs.length r 0) =
      some (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) out 0 0 r 2) ∧
    step (rewind a) (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) out 0 0 r 2) = none := by
  let f := wordTape (xs.map (bitSymbol (a := a)))
  let g := wordTape (ys.map (bitSymbol (a := a)))
  have hs := rewind_scan f g out (xs.length - 1) (xs.length - 1) r xs.length
    (fun j hj => word_bit_nonblank xs _ (by omega) (by omega))
  have he : (xs.length : ℤ) - 1 - xs.length = -1 := by omega
  rw [he] at hs
  have hr := rewind_right f g out (-1) (-1) r (by simp [f, wordTape])
  constructor
  · change run (rewind a) (xs.length + 2) (cfg f g out _ _ _ _) = _
    rw [show xs.length + 2 = 1 + xs.length + 1 by omega, run_add, run_add]
    rw [run_one, rewind_left f g out xs.length xs.length r 0 (Or.inl rfl)]
    simp only [Option.bind_some, hs, run_one]
    simpa using hr
  · simp [step, rewind, cfg]

def pad (a : ℕ) : Program 3 1 a := extend (BinaryPad.program a) 1

def prepare (a : ℕ) : Program 3 4 a := seq (pad a) (rewind a)

/-- Seven fixed control states and three fixed tapes, independent of widths. -/
def program (a : ℕ) : Program 3 7 a := seq (prepare a) (BinaryAdd.program a)

def width (xs ys : List Bool) : ℕ := max xs.length ys.length

def sumWord (xs ys : List Bool) : List Bool :=
  BinaryAdd.result false ((BinaryPad.padded xs (width xs ys)).zip (BinaryPad.padded ys (width xs ys)))

def runtime (xs ys : List Bool) : ℕ := 2 * width xs ys + 4 + (sumWord xs ys).length

private theorem pad_cfg (f g out : ℤ → Fin (a + 4)) (p q r : ℤ) :
    (BinaryPad.cfg f g p q).extend (⟨fun _ => r, fun _ => out⟩ : Tapes 1 a) = cfg f g out p q r 0 := by
  unfold Config.extend Tapes.append Config.tapes BinaryPad.cfg cfg
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem sumWord_value (xs ys : List Bool) : Counter.value (sumWord xs ys) = Counter.value xs + Counter.value ys := by
  have hl : (BinaryPad.padded xs (width xs ys)).length = (BinaryPad.padded ys (width xs ys)).length := by
    unfold width
    rw [BinaryPad.padded_length _ _ (Nat.le_max_left _ _), BinaryPad.padded_length _ _ (Nat.le_max_right _ _)]
  simpa [sumWord, BinaryAdd.bitValue, BinaryPad.padded_value] using BinaryAdd.result_value false _ _ hl

theorem sumWord_length (xs ys : List Bool) : (sumWord xs ys).length ≤ width xs ys + 1 := by
  have hx := BinaryPad.padded_length xs (width xs ys) (Nat.le_max_left _ _)
  have hy := BinaryPad.padded_length ys (width xs ys) (Nat.le_max_right _ _)
  simpa only [sumWord, hx] using BinaryAdd.result_length_le false _ _ (hx.trans hy.symm)

theorem runtime_le (xs ys : List Bool) : runtime xs ys ≤ 3 * width xs ys + 5 := by
  have := sumWord_length xs ys
  unfold runtime
  omega

/-- Complete arbitrary-width addition. All padding, backward head movement,
carry transitions, and both sequential joins appear in the exact runtime. -/
theorem add_exact (xs ys : List Bool) :
    let px := BinaryPad.padded xs (width xs ys)
    let py := BinaryPad.padded ys (width xs ys)
    let out := sumWord xs ys
    let final := Fin.natAdd 4 (BinaryAdd.finalState (BinaryAdd.overflow false (px.zip py)))
    run (program a) (runtime xs ys)
      (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol)) (fun _ => blank) 0 0 0 0) =
      some (cfg (wordTape (px.map bitSymbol)) (wordTape (py.map bitSymbol)) (wordTape (out.map bitSymbol))
        (width xs ys) (width xs ys) out.length final) ∧
    step (program a)
      (cfg (wordTape (px.map bitSymbol)) (wordTape (py.map bitSymbol)) (wordTape (out.map bitSymbol))
        (width xs ys) (width xs ys) out.length final) = none := by
  let px := BinaryPad.padded xs (width xs ys)
  let py := BinaryPad.padded ys (width xs ys)
  have hx : px.length = width xs ys := BinaryPad.padded_length _ _ (Nat.le_max_left _ _)
  have hy : py.length = width xs ys := BinaryPad.padded_length _ _ (Nat.le_max_right _ _)
  obtain ⟨hp, hph⟩ := BinaryPad.pad_exact (a := a) xs ys
  let extra : Tapes 1 a := ⟨fun _ => 0, fun _ _ => blank⟩
  have hp' := extend_run (BinaryPad.program a) extra hp
  have hph' := extend_halt (BinaryPad.program a) extra hph
  change run (pad a) _ _ = _ at hp'
  change step (pad a) _ = none at hph'
  dsimp only [extra] at hp' hph'
  rw [pad_cfg, pad_cfg] at hp'
  rw [pad_cfg] at hph'
  obtain ⟨hr, hrh⟩ := rewind_exact px py (fun _ => (blank : Fin (a + 4))) 0
  rw [hx] at hr
  have hprep := seq_run (pad a) (rewind a) hp' hph' hr
  have hpreph := seq_halt_right (pad a) (rewind a) hrh
  obtain ⟨_, _, ha, hah⟩ := BinaryAdd.add_to_blank (a := a) px py (hx.trans hy.symm)
  change run (BinaryAdd.program a) _ (cfg _ _ _ _ _ _ _) = some (cfg _ _ _ _ _ _ _) at ha
  change step (BinaryAdd.program a) (cfg _ _ _ _ _ _ _) = none at hah
  rw [hx, hy] at ha hah
  have htotal := seq_run (prepare a) (BinaryAdd.program a) hprep hpreph ha
  have hhalt := seq_halt_right (prepare a) (BinaryAdd.program a) hah
  have htime : max xs.length ys.length + 1 + (width xs ys + 2) + 1 +
      (BinaryAdd.result false (px.zip py)).length = runtime xs ys := by
    dsimp [runtime, sumWord, px, py, width]
    omega
  rw [htime] at htotal
  exact ⟨htotal, hhalt⟩

/-- The user-facing arithmetic contract needs only two raw input word tapes
and an initially blank output tape, without an equal-width assumption. -/
theorem add_hoare (xs ys : List Bool) :
    HoareTime (program a)
      (fun v => v = (cfg (wordTape (xs.map bitSymbol)) (wordTape (ys.map bitSymbol))
        (fun _ => blank) 0 0 0 (0 : Fin 7)).tapes)
      (fun v => ∃ px py out : List Bool,
        Counter.value px = Counter.value xs ∧ Counter.value py = Counter.value ys ∧
        Counter.value out = Counter.value xs + Counter.value ys ∧
        px.length = width xs ys ∧ py.length = width xs ys ∧ out.length ≤ width xs ys + 1 ∧
        v = (cfg (wordTape (px.map bitSymbol)) (wordTape (py.map bitSymbol)) (wordTape (out.map bitSymbol))
          (width xs ys) (width xs ys) out.length (0 : Fin 7)).tapes)
      (3 * width xs ys + 5) := by
  rintro v rfl
  obtain ⟨hr, hh⟩ := add_exact (a := a) xs ys
  exact ⟨_, _, runtime_le xs ys, hr, hh, BinaryPad.padded xs _, BinaryPad.padded ys _, sumWord xs ys,
    BinaryPad.padded_value _ _, BinaryPad.padded_value _ _, sumWord_value xs ys,
    BinaryPad.padded_length _ _ (Nat.le_max_left _ _), BinaryPad.padded_length _ _ (Nat.le_max_right _ _),
    sumWord_length xs ys, rfl⟩

end IntegerMultBounds.Machine.BinaryArithmetic

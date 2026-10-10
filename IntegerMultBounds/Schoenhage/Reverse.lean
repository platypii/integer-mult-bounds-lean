import IntegerMultBounds.Schoenhage.Ops

/-! Copying a word reversed. A two-tape machine scans the source's current
word to its separator, walks back over it writing each bit to the
destination, ends the new word with a separator, and steps the source past
the word. As a primitive (`Reverse.prim`, `revw`): the source advances one
word and the destination gains the reversed word (`runs_revw`). -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

/-- A two-tape bank. -/
def two (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) : Tapes 2 a :=
  ⟨fun i => if i.val = 0 then h0 else h1, fun i => if i.val = 0 then f0 else f1⟩

theorem enc_two (σ : Fin 2 → WTape) :
    enc (a := a) σ = two (σ 0).pos (σ 0).tape (σ 1).pos (σ 1).tape := by
  simp only [enc, two]
  congr 1 <;> funext x <;> fin_cases x <;> rfl

/-- The action writing `x0`, `x1` and moving by `m0`, `m1`. -/
def act2 (x0 : Fin (a + 4)) (m0 : Move) (x1 : Fin (a + 4)) (m1 : Move) : Fin 2 → Fin (a + 4) × Move :=
  fun i => if i.val = 0 then (x0, m0) else (x1, m1)

/-- One transition of a two-tape machine. -/
theorem step_two (M : FMachine 2 a) {s s' : M.S} {h0 h1 : ℤ} {f0 f1 : ℤ → Fin (a + 4)}
    (x0 : Fin (a + 4)) (m0 : Move) (x1 : Fin (a + 4)) (m1 : Move)
    (hδ : M.δ s (fun i => if i.val = 0 then f0 h0 else f1 h1) = some (s', act2 x0 m0 x1 m1)) :
    M.fstep ⟨s, two h0 f0 h1 f1⟩ = some ⟨s', two (h0 + m0.offset) (Function.update f0 h0 x0)
      (h1 + m1.offset) (Function.update f1 h1 x1)⟩ := by
  have hr : (fun i : Fin 2 => (two h0 f0 h1 f1 : Tapes 2 a).tape i ((two h0 f0 h1 f1 : Tapes 2 a).head i)) =
      fun i => if i.val = 0 then f0 h0 else f1 h1 := by
    funext i; simp only [two]; split_ifs <;> rfl
  simp only [FMachine.fstep, hr, hδ]
  congr 2
  simp only [two, act2, Tapes.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i; split_ifs <;> rfl
  · funext i j; split_ifs <;> simp_all [Function.update_apply]

theorem halt_two (M : FMachine 2 a) {s : M.S} {v : Tapes 2 a}
    (hδ : ∀ syms, M.δ s syms = none) : M.fstep ⟨s, v⟩ = none := by
  simp [FMachine.fstep, hδ]

namespace Reverse

inductive St where
  | scan | back | fwd | done
  deriving DecidableEq

instance : Fintype St := ⟨{.scan, .back, .fwd, .done}, by intro x; cases x <;> simp⟩

abbrev machine : FMachine 2 a where
  S := St
  start := .scan
  δ s syms := match s with
    | .scan => if syms 0 = separator then some (.back, act2 (syms 0) .left (syms 1) .stay)
        else some (.scan, act2 (syms 0) .right (syms 1) .stay)
    | .back => if syms 0 = blank ∨ syms 0 = separator then
          some (.fwd, act2 (syms 0) .right separator .right)
        else some (.back, act2 (syms 0) .left (syms 0) .right)
    | .fwd => if syms 0 = separator then some (.done, act2 (syms 0) .right (syms 1) .stay)
        else some (.fwd, act2 (syms 0) .right (syms 1) .stay)
    | .done => none

theorem rd0 (h0 h1 : ℤ) (f0 f1 : ℤ → Fin (a + 4)) :
    (fun i : Fin 2 => if i.val = 0 then f0 h0 else f1 h1) 0 = f0 h0 := rfl

theorem rd1 (h0 h1 : ℤ) (f0 f1 : ℤ → Fin (a + 4)) :
    (fun i : Fin 2 => if i.val = 0 then f0 h0 else f1 h1) 1 = f1 h1 := rfl

theorem bit_ne_sep (b : Bool) : bitSymbol (a := a) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator, Fin.ext_iff]

theorem bit_ne_blank (b : Bool) : bitSymbol (a := a) b ≠ blank := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- Scan right to the separator, then turn back. -/
theorem scan_run (f0 f1 : ℤ → Fin (a + 4)) (h1 : ℤ) :
    ∀ (n : ℕ) (h0 : ℤ), (∀ c : ℕ, c < n → f0 (h0 + c) ≠ separator) → f0 (h0 + n) = separator →
      (machine (a := a)).frun (n + 1) ⟨.scan, two h0 f0 h1 f1⟩ = some ⟨.back, two (h0 + n - 1) f0 h1 f1⟩
  | 0, h0, _, hs => by
    simp only [Nat.cast_zero, add_zero] at hs
    rw [FMachine.frun_one, step_two machine (s' := .back) (f0 h0) .left (f1 h1) .stay
      (by simp [machine, rd0, rd1, hs])]
    simp [Move.offset]; ring_nf
  | n + 1, h0, hns, hs => by
    have h0' : f0 h0 ≠ separator := by simpa using hns 0 (by omega)
    have ih := scan_run f0 f1 h1 n (h0 + 1) (fun c hc => by
      have := hns (c + 1) (by omega); push_cast at this; rwa [show h0 + 1 + c = h0 + (c + 1) by ring])
      (by push_cast at hs; rwa [show h0 + 1 + n = h0 + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_two machine (s' := .scan) (f0 h0) .right (f1 h1) .stay (by simp [machine, rd0, rd1, h0']))) ?_
    simp only [Function.update_eq_self, Move.offset, add_zero]
    convert ih using 4
    push_cast; ring

/-- Walk back over the bits `bs` (nearest first), writing them, then end the word. -/
theorem back_run (f0 : ℤ → Fin (a + 4)) :
    ∀ (bs : List Bool) (h0 h1 : ℤ) (f1 : ℤ → Fin (a + 4)),
      (∀ c : ℕ, (hc : c < bs.length) → f0 (h0 - c) = bitSymbol bs[c]) →
      (f0 (h0 - bs.length) = blank ∨ f0 (h0 - bs.length) = separator) →
      (machine (a := a)).frun (bs.length + 1) ⟨.back, two h0 f0 h1 f1⟩ =
        some ⟨.fwd, two (h0 - bs.length + 1) f0 (h1 + bs.length + 1)
          (putWord f1 h1 (bs.map bitSymbol ++ [separator]))⟩
  | [], h0, h1, f1, _, hb => by
    simp only [List.length_nil, Nat.cast_zero, sub_zero] at hb
    simp only [List.length_nil, zero_add, Nat.cast_zero, sub_zero, add_zero]
    rw [FMachine.frun_one, step_two machine (s' := .fwd) (f0 h0) .right separator .right
      (by simp [machine, rd0, rd1, hb])]
    simp [Move.offset, putWord]
  | b :: bs, h0, h1, f1, hc, hb => by
    have e0 : f0 h0 = bitSymbol b := by
      have := hc 0 (by simp)
      simp only [Nat.cast_zero, sub_zero, List.getElem_cons_zero] at this
      exact this
    have ih := back_run f0 bs (h0 - 1) (h1 + 1) (Function.update f1 h1 (bitSymbol b))
      (fun c hc' => by
        have := hc (c + 1) (by simp; omega); push_cast at this
        rwa [show h0 - 1 - c = h0 - (c + 1) by ring])
      (by simp only [List.length_cons] at hb; push_cast at hb; rwa [show h0 - 1 - bs.length = h0 - (bs.length + 1) by ring])
    rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by simp; omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_two machine (s' := .back) (f0 h0) .left (f0 h0) .right
        (by simp [machine, rd0, rd1, e0, bit_ne_blank, bit_ne_sep]))) ?_
    simp only [Function.update_eq_self, Move.offset, e0]
    have eu : Function.update f0 h0 (bitSymbol b) = f0 := by rw [← e0]; exact Function.update_eq_self _ _
    rw [eu]
    convert ih using 4
    all_goals first | (simp [putWord_cons]; done) | (simp; ring) | (push_cast; ring)

/-- Scan right to the separator and step past it. -/
theorem fwd_run (f0 f1 : ℤ → Fin (a + 4)) (h1 : ℤ) :
    ∀ (n : ℕ) (h0 : ℤ), (∀ c : ℕ, c < n → f0 (h0 + c) ≠ separator) → f0 (h0 + n) = separator →
      (machine (a := a)).frun (n + 1) ⟨.fwd, two h0 f0 h1 f1⟩ = some ⟨.done, two (h0 + n + 1) f0 h1 f1⟩
  | 0, h0, _, hs => by
    simp only [Nat.cast_zero, add_zero] at hs
    rw [FMachine.frun_one, step_two machine (s' := .done) (f0 h0) .right (f1 h1) .stay
      (by simp [machine, rd0, rd1, hs])]
    simp [Move.offset]
  | n + 1, h0, hns, hs => by
    have h0' : f0 h0 ≠ separator := by simpa using hns 0 (by omega)
    have ih := fwd_run f0 f1 h1 n (h0 + 1) (fun c hc => by
      have := hns (c + 1) (by omega); push_cast at this; rwa [show h0 + 1 + c = h0 + (c + 1) by ring])
      (by push_cast at hs; rwa [show h0 + 1 + n = h0 + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_two machine (s' := .fwd) (f0 h0) .right (f1 h1) .stay (by simp [machine, rd0, rd1, h0']))) ?_
    simp only [Function.update_eq_self, Move.offset, add_zero]
    convert ih using 4
    push_cast; ring

/-- The cell before the current word is blank or a separator. -/
theorem before_word (T : WTape) :
    T.tape (a := a) (T.pos - 1) = blank ∨ T.tape (a := a) (T.pos - 1) = separator := by
  rcases hl : T.left with _ | ⟨x, L'⟩
  · left; exact T.tape_neg _ (by simp [WTape.pos, hl])
  · right
    have := (⟨L', x :: T.right⟩ : WTape).tape_sep (a := a) rfl
    have e : (⟨L', x :: T.right⟩ : WTape).tape (a := a) = T.tape := by
      simp [WTape.tape, WTape.words, hl]
    have p : (⟨L', x :: T.right⟩ : WTape).pos + x.length = T.pos - 1 := by
      simp [WTape.pos, hl]; ring
    rwa [e, p] at this

theorem cells_single (v : List Bool) : cells (a := a) [v] = v.map bitSymbol ++ [separator] := by
  simp [cells, syms_cons, sym, Function.comp_def]

/-- Reverse: the source's current word, reversed, as a new word of the destination. -/
noncomputable abbrev prim : Prim a where
  s := 2
  hs := by omega
  M := machine
  pre σ := (σ 0).right ≠ [] ∧ (σ 1).right = []
  sem σ := fun i => if i.val = 0 then (σ 0).next else ⟨(σ 0).cur.reverse :: (σ 1).left, []⟩
  cost σ := 3 * (σ 0).cur.length + 10
  spec σ hpre := by
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_two]
    set T0 := σ 0
    set T1 := σ 1
    obtain ⟨w, R, hr⟩ : ∃ w R, T0.right = w :: R := by
      rcases h : T0.right with _ | ⟨w, R⟩
      · exact absurd h hpre.1
      · exact ⟨w, R, rfl⟩
    have hcur : T0.cur = w := by simp [WTape.cur, hr]
    set n := w.length
    have hbits : ∀ (c : ℕ) (hc : c < n), T0.tape (a := a) (T0.pos + c) = bitSymbol w[c] :=
      fun c hc => T0.tape_word hr c hc
    have hsep : T0.tape (a := a) (T0.pos + n) = separator := T0.tape_sep hr
    have s1 := scan_run (T0.tape (a := a)) T1.tape T1.pos n T0.pos
      (fun c hc => by rw [hbits c hc]; exact bit_ne_sep _) hsep
    have s2 := back_run (T0.tape (a := a)) w.reverse (T0.pos + n - 1) T1.pos T1.tape
      (fun c hc => by
        simp only [List.length_reverse] at hc
        rw [show T0.pos + n - 1 - c = T0.pos + ((n - 1 - c : ℕ) : ℤ) by push_cast [show c ≤ n - 1 by omega]; omega,
          hbits _ (by omega), List.getElem_reverse])
      (by rw [List.length_reverse, show T0.pos + n - 1 - n = T0.pos - 1 by ring]; exact before_word T0)
    rw [List.length_reverse, show T0.pos + n - 1 - n + 1 = T0.pos by ring] at s2
    have s3 := fwd_run (T0.tape (a := a)) (putWord T1.tape T1.pos (w.reverse.map bitSymbol ++ [separator]))
      (T1.pos + n + 1) n T0.pos (fun c hc => by rw [hbits c hc]; exact bit_ne_sep _) hsep
    refine ⟨(n + 1) + ((n + 1) + (n + 1)), ⟨.done, two (T0.pos + n + 1) T0.tape (T1.pos + n + 1)
      (putWord T1.tape T1.pos (w.reverse.map bitSymbol ++ [separator]))⟩, by rw [hcur]; omega,
      FMachine.frun_trans _ s1 (FMachine.frun_trans _ s2 s3), halt_two machine (fun _ => rfl), ?_⟩
    rw [enc_two]
    have c0 : ((0 : Fin 2) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 2) : ℕ) = 1 := rfl
    simp only [c0, c1, ↓reduceIte, one_ne_zero, hcur, T0.next_pos hr, T0.next_tape hr]
    have hput := T1.put_end (a := a) hpre.2 [w.reverse]
    rw [cells_single] at hput
    rw [hput]
    simp [two, WTape.pos, n]
    ring

end Reverse

/-- Two slots: source then destination. -/
def slotRev (s d : Fin t) : Fin 2 → Fin t := fun i => if i.val = 0 then s else d

theorem slotRev_inj {s d : Fin t} (h : s ≠ d) : Function.Injective (slotRev s d) := by
  intro i j hij
  simp only [slotRev] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> omega

/-- Copy the current word of `s`, reversed, to the end of `d`. -/
noncomputable def revw (s d : Fin t) (h : s ≠ d) : Cmd a t := .prim Reverse.prim (slotRev s d) (slotRev_inj h)

theorem upd_slotRev (σ : Fin t → WTape) {s d : Fin t} (h : s ≠ d) (τ : Fin 2 → WTape) :
    upd σ (slotRev s d) τ = Function.update (Function.update σ s (τ 0)) d (τ 1) := by
  funext x
  have hi := slotRev_inj h
  by_cases hxd : x = d
  · subst hxd
    rw [Function.update_self]
    have := upd_slot σ hi τ 1
    rwa [show slotRev s x 1 = x by simp [slotRev]] at this
  · rw [Function.update_of_ne hxd]
    by_cases hxs : x = s
    · subst hxs
      rw [Function.update_self]
      have := upd_slot σ hi τ 0
      rwa [show slotRev x d 0 = x by simp [slotRev]] at this
    · rw [Function.update_of_ne hxs]
      refine upd_other σ _ τ x (fun i hi => ?_)
      simp only [slotRev] at hi; split_ifs at hi <;> simp_all

theorem runs_revw {s d : Fin t} (h : s ≠ d) (σ : Fin t → WTape) {L R : List (List Bool)} {w : List Bool}
    (hs : σ s = ⟨L, w :: R⟩) (hd : (σ d).right = []) :
    Runs (a := a) (revw s d h) σ
      (· = Function.update (Function.update σ s ⟨w :: L, R⟩) d ⟨w.reverse :: (σ d).left, []⟩)
      (3 * w.length + 10) := by
  have hpre : Reverse.prim.pre (a := a) (σ ∘ slotRev s d) :=
    ⟨by simp [slotRev, hs], by simpa [slotRev] using hd⟩
  refine ⟨_, _, Exec.prim (P := Reverse.prim) hpre, ?_, ?_⟩
  · rw [upd_slotRev σ h]
    simp [slotRev, hs, WTape.next, WTape.cur]
  · simp [slotRev, hs, WTape.cur]

end IntegerMultBounds.Schoenhage

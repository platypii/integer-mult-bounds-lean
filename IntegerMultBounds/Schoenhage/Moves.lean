import IntegerMultBounds.Schoenhage.Cmd

/-! Head movements on one word tape: rewind to the first word, step back over
the previous word, and erase the whole tape. Each is a small finite-type
machine with an exact run. -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a : ℕ}

/-- A one-tape bank. -/
def one (h : ℤ) (f : ℤ → Fin (a + 4)) : Tapes 1 a := ⟨fun _ => h, fun _ => f⟩

theorem enc_one (σ : Fin 1 → WTape) : enc (a := a) σ = one (σ 0).pos (σ 0).tape := by
  simp only [enc, one]
  congr 1 <;> funext x <;> rw [Subsingleton.elim x 0]

namespace WTape

theorem tape_nonblank (T : WTape) (j : ℤ) (h0 : 0 ≤ j) (h1 : j < clen T.words) :
    T.tape (a := a) j ≠ blank := by
  rw [tape_eq, if_pos h0]
  have : j.toNat < (syms T.words).length := by rw [length_syms]; omega
  rw [List.getElem?_eq_getElem this]
  exact sym_ne_blank _

theorem tape_blank_ge (T : WTape) (j : ℤ) (h : clen T.words ≤ j) : T.tape (a := a) j = blank := by
  rw [tape_eq, if_pos (by have := Nat.zero_le (clen T.words); omega)]
  rw [List.getElem?_eq_none (by rw [length_syms]; omega)]
  rfl

theorem pos_le (T : WTape) : T.pos ≤ clen T.words := by
  simp [pos, words, clen_append, clen_reverse]

theorem clen_words (T : WTape) : clen T.words = clen T.left + clen T.right := by
  simp [words, clen_append, clen_reverse]

end WTape

/-- One transition that writes back the scanned symbol. -/
theorem step_one (M : FMachine 1 a) {s s' : M.S} {h : ℤ} {f : ℤ → Fin (a + 4)} (m : Move)
    (hδ : M.δ s (fun _ => f h) = some (s', fun _ => (f h, m))) :
    M.fstep ⟨s, one h f⟩ = some ⟨s', one (h + m.offset) f⟩ := by
  simp only [FMachine.fstep, one, hδ]
  congr 2
  simp only [Tapes.mk.injEq, true_and]
  funext i j; split_ifs with hj <;> simp [hj]

/-- One transition that writes a symbol. -/
theorem step_write (M : FMachine 1 a) {s s' : M.S} {h : ℤ} {f : ℤ → Fin (a + 4)} (x : Fin (a + 4))
    (m : Move) (hδ : M.δ s (fun _ => f h) = some (s', fun _ => (x, m))) :
    M.fstep ⟨s, one h f⟩ = some ⟨s', one (h + m.offset) (Function.update f h x)⟩ := by
  simp only [FMachine.fstep, one, hδ]
  congr 2
  simp only [Tapes.mk.injEq, true_and]
  funext i j; by_cases hj : j = h <;> simp [hj]

theorem halt_one (M : FMachine 1 a) {s : M.S} {v : Tapes 1 a}
    (hδ : ∀ syms, M.δ s syms = none) : M.fstep ⟨s, v⟩ = none := by
  simp [FMachine.fstep, hδ]

/-! ### Rewind -/

namespace Rewind

inductive St where
  | start | scan | done
  deriving DecidableEq

instance : Fintype St := ⟨{.start, .scan, .done}, by intro x; cases x <;> simp⟩

abbrev machine : FMachine 1 a where
  S := St
  start := .start
  δ s syms := match s with
    | .start => some (.scan, fun _ => (syms 0, .left))
    | .scan => if syms 0 = blank then some (.done, fun _ => (syms 0, .right))
        else some (.scan, fun _ => (syms 0, .left))
    | .done => none

theorem scan_run (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h - c) ≠ blank) → f (h - n) = blank →
      (machine (a := a)).frun (n + 1) ⟨.scan, one h f⟩ = some ⟨.done, one (h - n + 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb
    rw [FMachine.frun_one, step_one machine (s' := .done) .right (by simp [machine, hb])]
    simp [Move.offset]
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := scan_run f n (h - 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h - 1 - c = h - (c + 1) by ring])
      (by push_cast at hb; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega, FMachine.frun_add, FMachine.frun_one,
      step_one machine (s' := .scan) .left (by simp [machine, h0]), Option.bind_some]
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring

/-- Rewind: all words to the right of the head. -/
noncomputable def prim : Prim a where
  s := 1
  hs := by omega
  M := machine
  pre _ := True
  sem σ := fun _ => ⟨[], (σ 0).left.reverse ++ (σ 0).right⟩
  cost σ := clen (σ 0).left + 2
  spec σ _ := by
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_one]
    set T := σ 0
    refine ⟨1 + (clen T.left + 1), ⟨.done, one 0 T.tape⟩, by omega, ?_, halt_one machine (fun _ => rfl), ?_⟩
    · rw [FMachine.frun_add, FMachine.frun_one, step_one machine (s' := .scan) .left (by simp [machine]),
        Option.bind_some]
      have := scan_run (T.tape (a := a)) (clen T.left) (T.pos - 1)
        (fun c hc => T.tape_nonblank _ (by simp [WTape.pos]; omega)
          (by have := T.pos_le; simp [WTape.pos] at this ⊢; omega))
        (T.tape_neg _ (by simp [WTape.pos]))
      convert this using 3
      · simp [one]; rfl
      · simp [WTape.pos]
    · simp only [FMachine.Cfg.tapes]
      rw [enc_one]
      simp [one, WTape.pos, WTape.tape, WTape.words]

end Rewind

/-! ### Back -/

namespace Back

inductive St where
  | start | mid | scan | done
  deriving DecidableEq

instance : Fintype St := ⟨{.start, .mid, .scan, .done}, by intro x; cases x <;> simp⟩

abbrev machine : FMachine 1 a where
  S := St
  start := .start
  δ s syms := match s with
    | .start => some (.mid, fun _ => (syms 0, .left))
    | .mid => some (.scan, fun _ => (syms 0, .left))
    | .scan => if syms 0 = blank ∨ syms 0 = separator then some (.done, fun _ => (syms 0, .right))
        else some (.scan, fun _ => (syms 0, .left))
    | .done => none

theorem scan_run (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h - c) ≠ blank ∧ f (h - c) ≠ separator) →
      (f (h - n) = blank ∨ f (h - n) = separator) →
      (machine (a := a)).frun (n + 1) ⟨.scan, one h f⟩ = some ⟨.done, one (h - n + 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb
    rw [FMachine.frun_one, step_one machine (s' := .done) .right (by rcases hb with hb | hb <;> simp [machine, hb])]
    simp [Move.offset]
  | n + 1, h, hnb, hb => by
    have h0 := hnb 0 (by omega)
    simp only [Nat.cast_zero, sub_zero] at h0
    have ih := scan_run f n (h - 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h - 1 - c = h - (c + 1) by ring])
      (by push_cast at hb; rwa [show h - 1 - n = h - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega, FMachine.frun_add, FMachine.frun_one,
      step_one machine (s' := .scan) .left (by simp [machine, h0.1, h0.2]), Option.bind_some]
    convert ih using 4
    · simp [Move.offset]; ring
    · push_cast; ring

/-- Back: the previous word becomes current. -/
noncomputable def prim : Prim a where
  s := 1
  hs := by omega
  M := machine
  pre σ := (σ 0).left ≠ []
  sem σ := fun _ => ⟨(σ 0).left.tail, (σ 0).left.headD [] :: (σ 0).right⟩
  cost σ := ((σ 0).left.headD []).length + 3
  spec σ hpre := by
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_one]
    set T := σ 0
    obtain ⟨w, L, hl⟩ : ∃ w L, T.left = w :: L := by
      rcases h : T.left with _ | ⟨w, L⟩
      · exact absurd h hpre
      · exact ⟨w, L, rfl⟩
    have hp : T.pos = clen L + w.length + 1 := by simp [WTape.pos, hl]; ring
    -- the cells of `w` and the cell before it
    have hcell : ∀ (c : ℕ) (hc : c < w.length),
        T.tape (a := a) (clen L + c) = bitSymbol w[c] := by
      intro c hc
      have := (⟨L, w :: T.right⟩ : WTape).tape_word (a := a) rfl c hc
      simpa [WTape.tape, WTape.words, WTape.pos, hl] using this
    have hbefore : T.tape (a := a) (clen L - 1) = blank ∨ T.tape (a := a) (clen L - 1) = separator := by
      rcases L with _ | ⟨x, L'⟩
      · left; exact T.tape_neg _ (by simp)
      · right
        have := (⟨L', x :: w :: T.right⟩ : WTape).tape_sep (a := a) rfl
        simp only [WTape.tape, WTape.words, WTape.pos, hl, List.reverse_cons, List.append_assoc,
          List.cons_append, List.nil_append] at this ⊢
        convert this using 2; simp; ring
    refine ⟨1 + 1 + (w.length + 1), ⟨.done, one (clen L) T.tape⟩, by simp [hl]; omega, ?_,
      halt_one machine (fun _ => rfl), ?_⟩
    · refine FMachine.frun_trans _ (FMachine.frun_trans _
        (FMachine.frun_of_step _ (step_one machine (s' := .mid) .left (by simp [machine])))
        (FMachine.frun_of_step _ (step_one machine (s' := .scan) .left (by simp [machine])))) ?_
      have := scan_run (T.tape (a := a)) w.length (T.pos - 1 + -1)
        (fun c hc => by
          have e : ((w.length - 1 - c : ℕ) : ℤ) = w.length - 1 - c := by omega
          rw [show T.pos - 1 + -1 - c = clen L + ((w.length - 1 - c : ℕ) : ℤ) by
            rw [hp, e]; ring, hcell _ (by omega)]
          exact ⟨by cases w[w.length - 1 - c] <;> simp [bitSymbol, blank, Fin.ext_iff],
            by cases w[w.length - 1 - c] <;> simp [bitSymbol, separator, Fin.ext_iff]⟩)
        (by rw [show T.pos - 1 + -1 - w.length = clen L - 1 by rw [hp]; ring]; exact hbefore)
      convert this using 4
      · simp [Move.offset]; rw [hp]; ring
      · rw [hp]; ring
    · rw [enc_one]
      simp [one, WTape.pos, WTape.tape, WTape.words, hl]

end Back

/-! ### Clear -/

namespace Clear

inductive St where
  | scan | erase | done
  deriving DecidableEq

instance : Fintype St := ⟨{.scan, .erase, .done}, by intro x; cases x <;> simp⟩

abbrev machine : FMachine 1 a where
  S := St
  start := .scan
  δ s syms := match s with
    | .scan => if syms 0 = blank then some (.erase, fun _ => (blank, .left))
        else some (.scan, fun _ => (syms 0, .right))
    | .erase => if syms 0 = blank then some (.done, fun _ => (blank, .right))
        else some (.erase, fun _ => (blank, .left))
    | .done => none

theorem scan_run (f : ℤ → Fin (a + 4)) :
    ∀ (n : ℕ) (h : ℤ), (∀ c : ℕ, c < n → f (h + c) ≠ blank) → f (h + n) = blank →
      (machine (a := a)).frun (n + 1) ⟨.scan, one h f⟩ = some ⟨.erase, one (h + n - 1) f⟩
  | 0, h, _, hb => by
    simp only [Nat.cast_zero, add_zero] at hb
    rw [FMachine.frun_one, step_write machine (s' := .erase) blank .left (by simp [machine, hb])]
    have : Function.update f h blank = f := by rw [← hb]; simp
    simp [this, Move.offset]; ring
  | n + 1, h, hnb, hb => by
    have h0 : f h ≠ blank := by simpa using hnb 0 (by omega)
    have ih := scan_run f n (h + 1) (fun c hc => by
      have := hnb (c + 1) (by omega); push_cast at this; rwa [show h + 1 + c = h + (c + 1) by ring])
      (by push_cast at hb; rwa [show h + 1 + n = h + (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_one machine (s' := .scan) .right (by simp [machine, h0]))) ?_
    convert ih using 4
    · simp [Move.offset]
    · push_cast; ring

/-- The tape below `n`. -/
def below (f : ℤ → Fin (a + 4)) (n : ℤ) : ℤ → Fin (a + 4) := fun j => if j < n then f j else blank

theorem erase_run (f : ℤ → Fin (a + 4)) (hneg : ∀ j < 0, f j = blank) :
    ∀ (n : ℕ), (∀ j : ℕ, j < n → f j ≠ blank) →
      (machine (a := a)).frun (n + 1) ⟨.erase, one ((n : ℤ) - 1) (below f n)⟩ =
        some ⟨.done, one 0 (fun _ => blank)⟩
  | 0, _ => by
    have hb : below f 0 (-1) = blank := by simp [below, hneg]
    simp only [Nat.cast_zero, zero_sub]
    rw [FMachine.frun_one, step_write machine (s' := .done) blank .right (by simp [machine, hb])]
    congr 3
    · funext j; by_cases hj : j = -1
      · subst hj; simp
      · rw [Function.update_of_ne hj]; simp only [below]; split_ifs with h
        · exact hneg j h
        · rfl
  | n + 1, hnb => by
    have e : ((n + 1 : ℕ) : ℤ) = n + 1 := by push_cast; ring
    rw [e, show (n : ℤ) + 1 - 1 = n by ring]
    have h0 : below f ((n : ℤ) + 1) n ≠ blank := by
      simp only [below, show (n : ℤ) < n + 1 by omega, ↓reduceIte]
      exact hnb n (by omega)
    rw [FMachine.frun, step_write machine (s := .erase) (h := (n : ℤ)) (f := below f ((n : ℤ) + 1))
      (s' := .erase) blank .left (by simp [machine, h0]), Option.bind_some]
    have ih := erase_run f hneg n (fun j hj => hnb j (by omega))
    convert ih using 4
    · simp [Move.offset]; ring
    · funext j
      by_cases hj : j = n
      · subst hj; simp [below]
      · rw [Function.update_of_ne hj]; simp only [below]
        by_cases h1 : j < n <;> by_cases h2 : j < (n : ℤ) + 1 <;> simp [h1, h2] <;> omega

/-- Clear: erase the whole tape. -/
noncomputable def prim : Prim a where
  s := 1
  hs := by omega
  M := machine
  pre _ := True
  sem _ := fun _ => ⟨[], []⟩
  cost σ := 2 * clen (σ 0).words + 2
  spec σ _ := by
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_one]
    set T := σ 0
    set N := clen T.words
    have hbelow : below (T.tape (a := a)) N = T.tape := by
      funext j; simp only [below]; split_ifs with hj
      · rfl
      · exact (T.tape_blank_ge j (by omega)).symm
    have hpN : T.pos ≤ N := T.pos_le
    have hp0 : 0 ≤ T.pos := by simp [WTape.pos]
    refine ⟨((N - T.pos).toNat + 1) + (N + 1), ⟨.done, one 0 (fun _ => blank)⟩, by omega, ?_,
      halt_one machine (fun _ => rfl), ?_⟩
    · refine FMachine.frun_trans _ (scan_run (T.tape (a := a)) (N - T.pos).toNat T.pos
        (fun c hc => T.tape_nonblank _ (by omega) (by omega))
        (T.tape_blank_ge _ (by omega))) ?_
      have := erase_run (T.tape (a := a)) (fun j hj => T.tape_neg j hj) N
        (fun j hj => T.tape_nonblank _ (by omega) (by omega))
      rw [hbelow] at this
      convert this using 4; omega
    · rw [enc_one]
      simp only [one]
      congr 1
      funext _ j; simp [WTape.tape, WTape.words, cells, wordTape]

end Clear

/-! ### Emit -/

namespace Emit

/-- Write the cells `X` from the head on. -/
abbrev machine (X : List (Fin (a + 4))) : FMachine 1 a where
  S := Fin (X.length + 1)
  start := 0
  δ s syms := if h : s.val < X.length then
      some (⟨s.val + 1, by omega⟩, fun _ => (X[s.val], .right)) else none

theorem run (X : List (Fin (a + 4))) :
    ∀ (n : ℕ) (i : ℕ) (hi : i + n = X.length) (h : ℤ) (f : ℤ → Fin (a + 4)),
      (machine X).frun n ⟨⟨i, by omega⟩, one h f⟩ =
        some ⟨⟨X.length, by omega⟩, one (h + n) (putWord f h (X.drop i))⟩
  | 0, i, hi, h, f => by
    simp only [FMachine.frun, add_zero, Nat.cast_zero]
    have : i = X.length := by omega
    subst this
    simp [putWord]
  | n + 1, i, hi, h, f => by
    have hlt : i < X.length := by omega
    rw [FMachine.frun, step_write (machine X) (s' := ⟨i + 1, by omega⟩) X[i] .right
      (by simp [machine, hlt]), Option.bind_some]
    have := run X n (i + 1) (by omega) (h + 1) (Function.update f h X[i])
    convert this using 4
    · simp [Move.offset]
    · push_cast; ring
    · rw [List.drop_eq_getElem_cons hlt, putWord_cons]

/-- Emit: append fixed words at the end of the tape. -/
noncomputable def prim (ws : List (List Bool)) : Prim a where
  s := 1
  hs := by omega
  M := machine (cells ws)
  pre σ := (σ 0).right = []
  sem σ := fun _ => ⟨ws.reverse ++ (σ 0).left, []⟩
  cost _ := clen ws
  spec σ hpre := by
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_one]
    refine ⟨clen ws, _, le_rfl, run (cells ws) (clen ws) 0 (by simp [length_cells]) _ _,
      by simp [FMachine.fstep, machine], ?_⟩
    rw [enc_one]
    simp only [one, List.drop_zero]
    congr 1
    · funext _; simp [WTape.pos, clen_append, clen_reverse]; ring
    · funext _; exact (σ 0).put_end hpre ws

end Emit

end IntegerMultBounds.Schoenhage

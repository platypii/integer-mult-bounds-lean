import IntegerMultBounds.Schoenhage.Stream
import IntegerMultBounds.Schoenhage.Cmd

/-! The streaming machine as a word-program primitive. Every input tape must
have a current word; the output tape must be at its end. The inputs step
past their current words, and the emitted symbols, which must form whole
words, are appended to the output tape (in extend mode the first of them
continues the output's last word). -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm

variable {a r : ℕ}

namespace WTape

/-- The current word (empty at the end). -/
def cur (T : WTape) : List Bool := T.right.headD []

/-- Step past the current word. -/
def next (T : WTape) : WTape := ⟨T.cur :: T.left, T.right.tail⟩

/-- Append words at the end, optionally continuing the last word. -/
def put (T : WTape) (ext : Bool) (vs : List (List Bool)) : WTape :=
  match ext, T.left, vs with
  | true, u :: L, v :: vs' => ⟨vs'.reverse ++ (u ++ v) :: L, []⟩
  | _, L, vs => ⟨vs.reverse ++ L, []⟩

theorem next_pos (T : WTape) {w : List Bool} {R : List (List Bool)} (h : T.right = w :: R) :
    T.next.pos = T.pos + w.length + 1 := by
  simp [next, pos, cur, h]; ring

theorem next_tape (T : WTape) {w : List Bool} {R : List (List Bool)} (h : T.right = w :: R) :
    T.next.tape (a := a) = T.tape := by
  simp [next, tape, words, cur, h]

theorem Rd_of (T : WTape) {w : List Bool} {R : List (List Bool)} (h : T.right = w :: R) :
    Rd (T.tape (a := a)) T.pos w :=
  ⟨fun c hc => T.tape_word h c hc, T.tape_sep h⟩

end WTape

/-- The precondition of a streaming primitive. -/
def StreamPre (R : Rule r) (ext : Bool) (σ : Fin (r + 2) → WTape) : Prop :=
  (σ drv).right ≠ [] ∧ (∀ j, (σ (oth j)).right ≠ []) ∧ (σ out).right = [] ∧
  ∃ vs, output R (σ drv).cur (fun j => (σ (oth j)).cur) = syms vs ∧
    (ext = true → (σ out).left ≠ [] ∧ vs ≠ [])

/-- The effect of a streaming primitive. -/
def streamSem (R : Rule r) (ext : Bool) (σ : Fin (r + 2) → WTape) : Fin (r + 2) → WTape :=
  fun i => if i = out then
    (σ out).put ext (parse (output R (σ drv).cur (fun j => (σ (oth j)).cur)))
    else (σ i).next

theorem exists_cons {l : List (List Bool)} (h : l ≠ []) : ∃ w R, l = w :: R := by
  cases l with
  | nil => exact absurd rfl h
  | cons w R => exact ⟨w, R, rfl⟩

/-- The streaming primitive. -/
noncomputable abbrev streamPrim (R : Rule r) (ext : Bool) : Prim a where
  s := r + 2
  hs := by omega
  M := machine R ext
  pre := StreamPre R ext
  sem := streamSem R ext
  cost σ := time R (σ drv).cur (fun j => (σ (oth j)).cur)
  spec σ hpre := by
    obtain ⟨hdrv, hoth, hout, vs, hvs, hext⟩ := hpre
    apply FMachine.hoare
    intro v hv
    subst hv
    obtain ⟨w, R0, hw⟩ := exists_cons hdrv
    have hRd : Rd ((enc (a := a) σ).tape drv) ((enc (a := a) σ).head drv) (σ drv).cur := by
      simpa [enc, WTape.cur, hw] using (σ drv).Rd_of (a := a) hw
    have hRo : ∀ j, Rd ((enc (a := a) σ).tape (oth j)) ((enc (a := a) σ).head (oth j)) (σ (oth j)).cur :=
      fun j => by
        obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simpa [enc, WTape.cur, hw'] using (σ (oth j)).Rd_of (a := a) hw'
    obtain ⟨v', hrun, hhalt, htape, hhdrv, hhoth, hhout⟩ := stream_run R ext (enc σ) _ _ hRd hRo
    refine ⟨_, _, le_rfl, hrun, hhalt, ?_⟩
    simp only [FMachine.Cfg.tapes]
    rw [hvs] at htape hhout
    have hsem_out : streamSem R ext σ out = (σ out).put ext vs := by
      simp [streamSem, hvs, parse_syms]
    refine tapes_ext (funext fun i => ?_) (funext fun i => ?_)
    · rcases cases_tape i with rfl | ⟨j, rfl⟩ | rfl
      · rw [hhdrv]; simp only [enc, streamSem, drv_ne_out, ↓reduceIte]
        rw [(σ drv).next_pos hw]; simp [WTape.cur, hw]
      · rw [hhoth]
        obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simp only [enc, streamSem, oth_ne_out, ↓reduceIte]
        rw [(σ (oth j)).next_pos hw']; simp [WTape.cur, hw']
      · rw [hhout]; simp only [enc, hsem_out]
        cases ext with
        | false =>
          simp [WTape.put, WTape.pos, clen_append, clen_reverse, length_syms]; ring
        | true =>
          obtain ⟨hL, hV⟩ := hext rfl
          obtain ⟨u, L, hl⟩ := exists_cons hL
          obtain ⟨x, xs, hx⟩ := exists_cons hV
          subst hx
          simp [WTape.put, hl, WTape.pos, clen_append, clen_reverse, length_syms]; ring
    · rw [htape]
      rcases cases_tape i with rfl | ⟨j, rfl⟩ | rfl
      · simp only [drv_ne_out, ↓reduceIte, enc, streamSem]; rw [(σ drv).next_tape hw]
      · obtain ⟨w', R', hw'⟩ := exists_cons (hoth j)
        simp only [oth_ne_out, ↓reduceIte, enc, streamSem]; rw [(σ (oth j)).next_tape hw']
      · simp only [↓reduceIte, enc, hsem_out]
        cases ext with
        | false =>
          have := (σ out).put_end (a := a) hout vs
          simpa [WTape.put, cells] using this
        | true =>
          obtain ⟨hL, hV⟩ := hext rfl
          obtain ⟨u, L, hl⟩ := exists_cons hL
          obtain ⟨x, xs, hx⟩ := exists_cons hV
          subst hx
          have := (σ out).put_ext (a := a) hl hout x xs
          simpa [WTape.put, hl, cells] using this

end IntegerMultBounds.Schoenhage

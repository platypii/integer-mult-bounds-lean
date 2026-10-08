import IntegerMultBounds.Machine.Composition

/-! Time-bounded contracts for literal programs. Tape predicates include head
positions and all cells, so composition retains exact frame and cleanup facts.
All contracts quantify over actual `run` witnesses and a genuine halt. -/

namespace IntegerMultBounds.Machine

variable {t q r a : ℕ}

/-- Tape data independent of the internal finite control. -/
structure Tapes (t a : ℕ) where
  head : Fin t → ℤ
  tape : Fin t → ℤ → Fin (a + 4)

def Config.tapes (c : Config t q a) : Tapes t a := ⟨c.head, c.tape⟩

def Tapes.start (v : Tapes t a) (M : Program t q a) : Config t q a :=
  ⟨M.start, v.head, v.tape⟩

abbrev TapePred (t a : ℕ) := Tapes t a → Prop

/-- Starting with any tapes satisfying `pre`, the program halts within the
stated number of actual transitions and establishes `post`. -/
def HoareTime (M : Program t q a) (pre post : TapePred t a) (bound : ℕ) : Prop :=
  ∀ v, pre v → ∃ k c, k ≤ bound ∧ run M k (v.start M) = some c ∧
    step M c = none ∧ post c.tapes

theorem HoareTime.consequence {M : Program t q a}
    {pre pre' post post' : TapePred t a} {b b' : ℕ}
    (h : HoareTime M pre post b) (hpre : ∀ v, pre' v → pre v)
    (hpost : ∀ v, post v → post' v) (hb : b ≤ b') :
    HoareTime M pre' post' b' := by
  intro v hv
  obtain ⟨k, c, hk, hr, hh, hp⟩ := h v (hpre v hv)
  exact ⟨k, c, hk.trans hb, hr, hh, hpost c.tapes hp⟩

/-- Composition uses the exact one-step, tape-preserving connection. -/
theorem HoareTime.seq {M : Program t q a} {N : Program t r a}
    {pre middle post : TapePred t a} {b₁ b₂ : ℕ}
    (hM : HoareTime M pre middle b₁) (hN : HoareTime N middle post b₂) :
    HoareTime (seq M N) pre post (b₁ + 1 + b₂) := by
  intro v hv
  obtain ⟨k, c, hk, hr, hh, hp⟩ := hM v hv
  obtain ⟨l, d, hl, hs, hd, hpost⟩ := hN c.tapes hp
  refine ⟨k + 1 + l, d.mapState (Fin.natAdd q), by omega, ?_,
    seq_halt_right M N hd, hpost⟩
  exact seq_run M N hr hh hs

/-- The existing scan has a contract about every cell of an arbitrary tape,
not merely its encoded prefix. -/
theorem scanRight_hoare (f : ℤ → Fin 4) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f j ≠ blank) (hend : f n = blank) :
    HoareTime scanRight
      (fun v => v.head = (fun _ => 0) ∧ v.tape = (fun _ => f))
      (fun v => v.head = (fun _ => (n : ℤ)) ∧ v.tape = (fun _ => f)) n := by
  rintro ⟨head, tape⟩ ⟨rfl, rfl⟩
  obtain ⟨hr, hh⟩ := scan_exact f n h hend
  exact ⟨n, scanConfig f n, le_rfl, hr, hh, rfl, rfl⟩

end IntegerMultBounds.Machine

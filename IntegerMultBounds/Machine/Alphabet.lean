import IntegerMultBounds.Machine.Hoare

/-! Change a literal machine's finite alphabet through an encoding with a
left-inverse decoder. Encoded runs, their exact transition counts, and actual
halting are preserved. The initial-segment instance adds finitely many marker
symbols while preserving the existing blank, bits, and separator. -/

namespace IntegerMultBounds.Machine.Alphabet

variable {t q a b : ℕ}

/-- A finite symbol encoding, with a total decoder specified even off its image.
Only the left-inverse law is needed for exact simulation on encoded tapes. -/
structure Encoding (a b : ℕ) where
  encode : Fin (a + 4) → Fin (b + 4)
  decode : Fin (b + 4) → Fin (a + 4)
  decode_encode : ∀ x, decode (encode x) = x

theorem Encoding.injective (e : Encoding a b) : Function.Injective e.encode :=
  Function.LeftInverse.injective e.decode_encode

def mapConfig (e : Encoding a b) (c : Config t q a) : Config t q b :=
  ⟨c.state, c.head, fun i j => e.encode (c.tape i j)⟩

def mapTapes (e : Encoding a b) (v : Tapes t a) : Tapes t b :=
  ⟨v.head, fun i j => e.encode (v.tape i j)⟩

/-- This changes only finite symbol operations inside the transition table. -/
def program (e : Encoding a b) (M : Program t q a) : Program t q b where
  tapes_pos := M.tapes_pos
  start := M.start
  transition := fun state symbols =>
    (M.transition state (fun i => e.decode (symbols i))).map
      (fun (state', action) => (state', fun i => (e.encode (action i).1, (action i).2)))

theorem map_step (e : Encoding a b) (M : Program t q a) (c : Config t q a) :
    step (program e M) (mapConfig e c) = (step M c).map (mapConfig e) := by
  unfold step
  simp only [program, mapConfig, e.decode_encode]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v =>
    rcases v with ⟨state', action⟩
    simp only [Option.map_some]
    congr 1
    congr 1
    funext i j
    dsimp only
    by_cases hj : j = c.head i <;> simp [hj]

/-- The entire optional result commutes with encoding, including failed runs. -/
theorem map_run (e : Encoding a b) (M : Program t q a) (k : ℕ)
    (c : Config t q a) :
    run (program e M) k (mapConfig e c) = (run M k c).map (mapConfig e) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [run, map_step]
    cases hs : step M c with
    | none => rfl
    | some d => simpa only [Option.map_some, Option.bind_some] using ih d

theorem map_success (e : Encoding a b) (M : Program t q a)
    {k : ℕ} {c d : Config t q a} (h : run M k c = some d) :
    run (program e M) k (mapConfig e c) = some (mapConfig e d) := by
  rw [map_run, h]
  rfl

theorem map_halt_iff (e : Encoding a b) (M : Program t q a) (c : Config t q a) :
    step (program e M) (mapConfig e c) = none ↔ step M c = none := by
  rw [map_step]
  exact Option.map_eq_none_iff

/-- Time contracts retain their bound exactly under alphabet encoding. -/
theorem map_hoare (e : Encoding a b) {M : Program t q a}
    {pre post : TapePred t a} {bound : ℕ} (h : HoareTime M pre post bound) :
    HoareTime (program e M)
      (fun v => ∃ original, pre original ∧ v = mapTapes e original)
      (fun v => ∃ original, post original ∧ v = mapTapes e original) bound := by
  rintro v ⟨original, hp, rfl⟩
  obtain ⟨k, c, hk, hr, hh, hpost⟩ := h original hp
  exact ⟨k, mapConfig e c, hk, map_success e M hr,
    (map_halt_iff e M c).mpr hh, c.tapes, hpost, rfl⟩

/-- Observe an arbitrary larger-alphabet configuration through the decoder.
Foreign symbols need not be absent from its unvisited cells. -/
def decodeConfig (e : Encoding a b) (c : Config t q b) : Config t q a :=
  ⟨c.state, c.head, fun i j => e.decode (c.tape i j)⟩

def decodeTapes (e : Encoding a b) (v : Tapes t b) : Tapes t a :=
  ⟨v.head, fun i j => e.decode (v.tape i j)⟩

/-- Decoding commutes with every step, even on non-encoded configurations.
A foreign symbol under a head is interpreted by the decoder and can be replaced
by an encoded symbol; this theorem does not assert preservation of such cells. -/
theorem decode_step (e : Encoding a b) (M : Program t q a) (c : Config t q b) :
    (step (program e M) c).map (decodeConfig e) = step M (decodeConfig e c) := by
  unfold step
  simp only [program, decodeConfig]
  cases ht : M.transition c.state (fun i => e.decode (c.tape i (c.head i))) with
  | none => rfl
  | some v =>
    rcases v with ⟨state', action⟩
    simp only [Option.map_some, decodeConfig]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = c.head i <;> simp [hj, e.decode_encode]

theorem decode_run (e : Encoding a b) (M : Program t q a) (k : ℕ)
    (c : Config t q b) :
    (run (program e M) k c).map (decodeConfig e) = run M k (decodeConfig e c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [run, ← decode_step]
    cases hs : step (program e M) c with
    | none => rfl
    | some d => simpa only [Option.map_some, Option.bind_some] using ih d

theorem decode_halt_iff (e : Encoding a b) (M : Program t q a) (c : Config t q b) :
    step (program e M) c = none ↔ step M (decodeConfig e c) = none := by
  rw [← decode_step]
  exact Option.map_eq_none_iff.symm

/-- A successful source run from decoded tapes witnesses an actual run on the
original larger-alphabet tapes at exactly the same cost. -/
theorem decode_success (e : Encoding a b) (M : Program t q a)
    {k : ℕ} {c : Config t q b} {d : Config t q a}
    (h : run M k (decodeConfig e c) = some d) :
    ∃ result, run (program e M) k c = some result ∧ decodeConfig e result = d := by
  rw [← decode_run] at h
  cases hr : run (program e M) k c with
  | none => simp [hr] at h
  | some result =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    exact ⟨result, rfl, h⟩

/-- Contracts expressed through decoding apply to arbitrary larger-alphabet
tapes. Only the decoded postcondition is promised, so foreign marker preservation
must be supplied separately from cell-locality or a stronger invariant. -/
theorem decode_hoare (e : Encoding a b) {M : Program t q a}
    {pre post : TapePred t a} {bound : ℕ} (h : HoareTime M pre post bound) :
    HoareTime (program e M) (fun v => pre (decodeTapes e v))
      (fun v => post (decodeTapes e v)) bound := by
  intro v hv
  obtain ⟨k, c, hk, hr, hh, hp⟩ := h (decodeTapes e v) hv
  obtain ⟨result, hresult, hdecode⟩ := decode_success e M
    (c := v.start (program e M)) hr
  refine ⟨k, result, hk, hresult, ?_, ?_⟩
  · apply (decode_halt_iff e M result).mpr
    rw [hdecode]
    exact hh
  · change post (decodeConfig e result).tapes
    rw [hdecode]
    exact hp

/-- The first `a + 4` symbols retain their numerical codes. Extra symbols decode
as blank; encoded configurations never read this fallback branch. -/
def widen (a extra : ℕ) : Encoding a (a + extra) where
  encode := fun x => ⟨x.val, by have := x.isLt; omega⟩
  decode := fun x => if h : x.val < a + 4 then ⟨x.val, h⟩ else blank
  decode_encode := by intro x; simp [x.isLt]

@[simp] theorem widen_blank (a extra : ℕ) :
    (widen a extra).encode blank = blank := rfl

@[simp] theorem widen_bitSymbol (a extra : ℕ) (bit : Bool) :
    (widen a extra).encode (bitSymbol bit) = bitSymbol bit := rfl

@[simp] theorem widen_separator (a extra : ℕ) :
    (widen a extra).encode separator = separator := rfl

end IntegerMultBounds.Machine.Alphabet

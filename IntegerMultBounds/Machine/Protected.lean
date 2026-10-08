import IntegerMultBounds.Machine.Alphabet

/-! Exact alphabet simulation on a region of each tape. Cells outside the region
may contain arbitrary foreign symbols, including left sentinels, and are retained
literally. Region membership is a proof condition on the source head trajectory;
it is not an extra primitive or an oracle in the transition table. -/

namespace IntegerMultBounds.Machine.Alphabet

variable {t q a b : ℕ}

/-- Encode the working region and retain arbitrary larger-alphabet contents
outside it. This is a specification of configurations, not a machine operation. -/
noncomputable def overlay (e : Encoding a b) (region : Fin t → ℤ → Prop)
    (outside : Fin t → ℤ → Fin (b + 4)) (c : Config t q a) : Config t q b := by
  classical
  exact ⟨c.state, c.head, fun i j => if region i j then e.encode (c.tape i j)
    else outside i j⟩

@[simp] theorem overlay_head (e : Encoding a b) (region : Fin t → ℤ → Prop)
    (outside : Fin t → ℤ → Fin (b + 4)) (c : Config t q a) :
    (overlay e region outside c).head = c.head := rfl

theorem overlay_outside (e : Encoding a b) (region : Fin t → ℤ → Prop)
    (outside : Fin t → ℤ → Fin (b + 4)) (c : Config t q a)
    (i : Fin t) (j : ℤ) (h : ¬ region i j) :
    (overlay e region outside c).tape i j = outside i j := by
  simp [overlay, h]

/-- Only scanned cells need lie in the encoded region for one exact step.
The outside contents, including symbols not in the encoding's image, survive. -/
theorem overlay_step (e : Encoding a b) (M : Program t q a)
    (region : Fin t → ℤ → Prop) (outside : Fin t → ℤ → Fin (b + 4))
    (c : Config t q a) (hregion : ∀ i, region i (c.head i)) :
    step (program e M) (overlay e region outside c) =
      (step M c).map (overlay e region outside) := by
  classical
  unfold step
  simp only [program, overlay, hregion, ↓reduceIte, e.decode_encode]
  cases ht : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => rfl
  | some v =>
    rcases v with ⟨state', action⟩
    simp only [Option.map_some]
    congr 1
    congr 1
    funext i j
    dsimp only
    by_cases hj : j = c.head i
    · subst j; simp [hregion]
    · by_cases hr : region i j <;> simp [hj, hr]

/-- The proof-side footprint condition includes precisely the configurations
that take successful steps; the endpoint is treated separately for halting. -/
def VisitsWithin (M : Program t q a) (region : Fin t → ℤ → Prop)
    (k : ℕ) (c : Config t q a) : Prop :=
  ∀ m d, m < k → run M m c = some d → ∀ i, region i (d.head i)

/-- Reconstruct the entire target tape, not just its decoded observation, with
exactly the source runtime. Every outside cell is retained literally. -/
theorem overlay_run (e : Encoding a b) (M : Program t q a)
    (region : Fin t → ℤ → Prop) (outside : Fin t → ℤ → Fin (b + 4))
    {k : ℕ} {c d : Config t q a} (h : run M k c = some d)
    (hregion : VisitsWithin M region k c) :
    run (program e M) k (overlay e region outside c) =
      some (overlay e region outside d) := by
  induction k generalizing c with
  | zero =>
    have hcd : c = d := Option.some.inj h
    subst d
    rfl
  | succ k ih =>
    obtain ⟨next, hstep, hrun⟩ := Option.bind_eq_some_iff.mp h
    have hhead : ∀ i, region i (c.head i) := hregion 0 c (by omega) rfl
    have htail : VisitsWithin M region k next := by
      intro m z hm hz
      apply hregion (m + 1) z (by omega)
      simp only [run, hstep, Option.bind_some, hz]
    simp only [run, overlay_step e M region outside c hhead, hstep,
      Option.map_some, Option.bind_some]
    exact ih hrun htail

theorem overlay_halt (e : Encoding a b) (M : Program t q a)
    (region : Fin t → ℤ → Prop) (outside : Fin t → ℤ → Fin (b + 4))
    {c : Config t q a} (h : step M c = none)
    (hregion : ∀ i, region i (c.head i)) :
    step (program e M) (overlay e region outside c) = none := by
  rw [overlay_step e M region outside c hregion, h]
  rfl

/-- An exact halted execution with an arbitrary protected frame of tape cells.
The final read must also stay in-region: a foreign marker at the halt position
could otherwise decode to a different stop symbol. -/
theorem overlay_exact (e : Encoding a b) (M : Program t q a)
    (region : Fin t → ℤ → Prop) (outside : Fin t → ℤ → Fin (b + 4))
    {k : ℕ} {c d : Config t q a} (h : run M k c = some d)
    (hhalt : step M d = none)
    (hregion : ∀ m z, m ≤ k → run M m c = some z → ∀ i, region i (z.head i)) :
    run (program e M) k (overlay e region outside c) =
      some (overlay e region outside d) ∧
    step (program e M) (overlay e region outside d) = none ∧
    ∀ i j, ¬ region i j → (overlay e region outside d).tape i j = outside i j := by
  refine ⟨overlay_run e M region outside h
    (fun m z hm hz => hregion m z (by omega) hz),
    overlay_halt e M region outside hhalt (hregion k d le_rfl h), ?_⟩
  exact fun i j hj => overlay_outside e region outside d i j hj

/-- Tape-only version for contracts, retaining the same arbitrary outside frame. -/
noncomputable def overlayTapes (e : Encoding a b) (region : Fin t → ℤ → Prop)
    (outside : Fin t → ℤ → Fin (b + 4)) (v : Tapes t a) : Tapes t b := by
  classical
  exact ⟨v.head, fun i j => if region i j then e.encode (v.tape i j) else outside i j⟩

/-- Lift a source contract together with its proved head footprint. The target
postcondition preserves actual outside symbols, not merely their decodings. -/
theorem overlay_hoare (e : Encoding a b) {M : Program t q a}
    (region : Fin t → ℤ → Prop) (outside : Fin t → ℤ → Fin (b + 4))
    {pre post : TapePred t a} {bound : ℕ} (h : HoareTime M pre post bound)
    (hregion : ∀ v, pre v → ∀ m z, m ≤ bound → run M m (v.start M) = some z →
      ∀ i, region i (z.head i)) :
    HoareTime (program e M)
      (fun v => ∃ original, pre original ∧ v = overlayTapes e region outside original)
      (fun v => ∃ original, post original ∧ v = overlayTapes e region outside original)
      bound := by
  rintro v ⟨original, hp, rfl⟩
  obtain ⟨k, c, hk, hr, hh, hpost⟩ := h original hp
  obtain ⟨hrun, hhalt, _⟩ := overlay_exact e M region outside hr hh
    (fun m z hm hz => hregion original hp m z (hm.trans hk) hz)
  exact ⟨k, overlay e region outside c, hk, hrun, hhalt, c.tapes, hpost, rfl⟩

end IntegerMultBounds.Machine.Alphabet

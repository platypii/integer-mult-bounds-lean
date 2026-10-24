module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderValue

/-!
# Fixed lists of actual higher fields

Enumerate a consecutive run of the unchanged field bank. The suffix above a
rotation target forms a contiguous header starting immediately above that target,
including all gap and spectator fields and allowing zero-width fields.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

/-- A consecutive run, defined structurally on its fixed field count. -/
def fieldRun {nf : ℕ} (start : ℕ) : (count : ℕ) → start + count ≤ nf → List (Fin nf)
  | 0, _ => []
  | count + 1, h => ⟨start, by omega⟩ :: fieldRun (start + 1) count (by omega)

theorem fieldRun_length {nf : ℕ} (start count : ℕ) (h : start + count ≤ nf) :
    (fieldRun start count h).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [fieldRun, List.length_cons, ih]

theorem fieldRun_chain {nf : ℕ} (len : Fin nf → ℕ) (count start o : ℕ)
    (h : start + count ≤ nf)
    (hstart : ∀ hs : start < nf, fieldOff len ⟨start, hs⟩ = o) :
    HeaderChain len o (fieldRun start count h) := by
  induction count generalizing start o with
  | zero => trivial
  | succ count ih =>
    change fieldOff len ⟨start, _⟩ = o ∧
      HeaderChain len (o + len ⟨start, _⟩) (fieldRun (start + 1) count _)
    refine ⟨hstart _, ih (start + 1) _ (by omega) ?_⟩
    intro hs
    rw [fieldOff_succ len start hs, hstart]

/-- All actual fields above the rotated field, in increasing significance. -/
def higherFields {nf : ℕ} (ft : Fin nf) : List (Fin nf) :=
  fieldRun (ft.val + 1) (nf - (ft.val + 1)) (by omega)

theorem higherFields_length {nf : ℕ} (ft : Fin nf) :
    (higherFields ft).length = nf - (ft.val + 1) := fieldRun_length _ _ _

theorem higherFields_chain {nf : ℕ} (len : Fin nf → ℕ) (ft : Fin nf) :
    HeaderChain len (fieldOff len ft + len ft) (higherFields ft) := by
  apply fieldRun_chain
  intro hs
  simpa using fieldOff_succ len ft.val hs

theorem fieldRun_mem {nf : ℕ} (count start : ℕ) (h : start + count ≤ nf) (f : Fin nf) :
    f ∈ fieldRun start count h ↔ start ≤ f.val ∧ f.val < start + count := by
  induction count generalizing start with
  | zero => simp [fieldRun]
  | succ count ih =>
    simp only [fieldRun, List.mem_cons, ih, Fin.ext_iff]
    omega

@[simp] theorem higherFields_mem {nf : ℕ} (ft f : Fin nf) :
    f ∈ higherFields ft ↔ ft < f := by
  simp only [higherFields, fieldRun_mem, Fin.lt_def]
  omega

/-- Every field in a contiguous header lies wholly inside its actual bit window. -/
theorem HeaderChain.bounds {nf : ℕ} {len : Fin nf → ℕ} {fields : List (Fin nf)} {o : ℕ}
    (hchain : HeaderChain len o fields) {f : Fin nf} (hf : f ∈ fields) :
    o ≤ fieldOff len f ∧
      fieldOff len f + len f ≤ o + (fields.map len).sum := by
  induction fields generalizing o with
  | nil => simp at hf
  | cons g gs ih =>
    obtain ⟨hoff, hrest⟩ := hchain
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hf with rfl | hf
    · rw [hoff]; omega
    · have hb := ih hrest hf
      omega

/-- Relative windows for any actual source field above the rotation target. -/
theorem higherFields_window {nf : ℕ} (len : Fin nf → ℕ) (ft f : Fin nf) (hf : ft < f) :
    let o := fieldOff len ft + len ft
    o + (fieldOff len f - o) = fieldOff len f ∧
      (fieldOff len f - o) + len f ≤ ((higherFields ft).map len).sum := by
  have hb := (higherFields_chain len ft).bounds ((higherFields_mem ft f).2 hf)
  dsimp only
  omega

end IntegerMultBounds.MathlibTM2.Routing

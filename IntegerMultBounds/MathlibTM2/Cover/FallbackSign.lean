module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidual

/-! The residue-class itinerary determines the anchor sign at every positive atom width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix Itinerary
variable {q w n : ℕ}

/-- The table entry for the sign bit uses only the residue matrix and its pivot itinerary. -/
noncomputable def negativeAnchor (p : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) (ZMod q)) : Bool :=
  decide ((run p M n).det ≠ 1)

theorem anchor_of_itinerary (hodd : 2 < q) (hw : 0 < w) (p : Fin n → Fin n)
    (G : Matrix (Fin n) (Fin n) (ZMod (q^w))) (hv : Valid p G n)
    (hg : G.det = 1 ∨ G.det = -1) :
    (run p G n).det = if negativeAnchor p ((LabelRing.res q w hw).mapMatrix G) then -1 else 1 := by
  let φ := LabelRing.res q w hw
  have hmap : φ (run p G n).det = (run p (φ.mapMatrix G) n).det := by
    rw [RingHom.map_det,← run_map φ p G n hv]
  obtain ⟨E,hE,he,_,_⟩ := run_spec p G n le_rfl hv
  have hs : (run p G n).det = 1 ∨ (run p G n).det = -1 := by
    rw [← he,det_mul]
    rcases hE.det_sign with h | h <;> rcases hg with e | e <;> simp [h,e]
  let : Fact (2 < q) := ⟨hodd⟩
  change _ = if decide ((run p (φ.mapMatrix G) n).det ≠ 1) then -1 else 1
  rw [← hmap]
  rcases hs with h | h <;> simp [h,ZMod.neg_one_ne_one]

/-- With that bit fixed, the remaining diagonal factors are the reciprocal pairs on
the non-anchor coordinates. Elimination follows the specified class itinerary. -/
theorem itinerary_pairs (hodd : 2 < q) (hw : 0 < w) (p : Fin (n+1) → Fin (n+1))
    (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (q^w))) (hv : Valid p G (n+1))
    (hg : G.det = 1 ∨ G.det = -1) :
    let s : (ZMod (q^w))ˣ := if negativeAnchor p ((LabelRing.res q w hw).mapMatrix G) then -1 else 1
    ∃ E, ∃ d : Fin n → (ZMod (q^w))ˣ, Elim ((n+1)*n) (n+1) E ∧
      E * G = diagonal (fun j => (((Fin.cons s (fun _ => 1) * ∏ i, pair i (d i) :
        Fin (n+1) → (ZMod (q^w))ˣ) j : (ZMod (q^w))ˣ) : ZMod (q^w))) := by
  obtain ⟨E,hE,he,clear,units⟩ := run_spec p G (n+1) le_rfl hv
  let d (i : Fin (n+1)) := (units i i.isLt).unit
  have diag : run p G (n+1) = diagonal (fun i => (d i : ZMod (q^w))) := by
    ext i j
    by_cases h : i = j
    · subst j
      rw [diagonal_apply_eq]
      exact (units i i.isLt).unit_spec.symm
    · rw [diagonal_apply_ne _ h]
      exact clear i j j.isLt h
  have hs := anchor_of_itinerary hodd hw p G hv hg
  rw [diag,det_diagonal] at hs
  have prod : (∏ i, d i) = (if negativeAnchor p ((LabelRing.res q w hw).mapMatrix G) then -1 else 1) := by
    apply Units.ext
    cases h : negativeAnchor p ((LabelRing.res q w hw).mapMatrix G) <;> rw [h] at hs <;> simpa [Units.coe_prod] using hs
  refine ⟨E,fun i => d i.succ,by simpa using hE,?_⟩
  rw [he,diag,← prod,← unit_pairs d]

end IntegerMultBounds.MathlibTM2.Cover.Fallback

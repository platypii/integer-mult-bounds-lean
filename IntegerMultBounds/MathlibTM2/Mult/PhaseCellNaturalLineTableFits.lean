module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineTables

/-! Factor-step fit proofs imply every retained triangular coefficient fits. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem FacFits.tables {q w K : ℕ} {rows : List (List ℤ)} (h : FacFits w q K rows) :
    (∀ x ∈ lcolZ q K rows, Fits w (⟨x,0⟩ : GaussianInt)) ∧
    (∀ x ∈ rows.headD [], Fits w (⟨x,0⟩ : GaussianInt)) ∧
    Fits w (⟨newtonZ q (facPiv rows) K,0⟩ : GaussianInt) := by
  cases rows with
  | nil => simp [FacFits] at h
  | cons row rest =>
    cases row with
    | nil => simp [FacFits] at h
    | cons c tail =>
      change Fits w (⟨c,0⟩ : GaussianInt) ∧ _ at h
      refine ⟨?_,?_,h.2.2.1⟩
      · intro x hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
        exact (h.2.2.2.2 r hr).2
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h.1
        · exact h.2.2.2.1 x hx

theorem integer_getD_fits {w : ℕ} (xs : List ℤ)
    (h : ∀ x ∈ xs, Fits w (⟨x,0⟩ : GaussianInt)) (i : ℕ) :
    Fits w (⟨xs.getD i 0,0⟩ : GaussianInt) := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    constructor <;> simp

theorem naturalLineTables_widths (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) (hq : 2 ≤ q)
    (hband : BandFrom W (gvM q AZ) 0) :
    (∀ c ∈ naturalLineLc q K W N AZ, c.length = W) ∧
    (∀ c ∈ naturalLineUc q K W N AZ, c.length = W) := by
  constructor
  · intro c hc
    rw [naturalLineLc,factorRowsZ_run q K W hq AZ hband N,List.map_map] at hc
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hc
    simp
  · intro c hc
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hc
    simp [ucolZ]

theorem naturalLineTables_fits (q w K W N : ℕ) (AZ : ℕ → ℕ → ℤ)
    (hfit : ∀ j < N, FacFits w q K (facState q K (windowZ W AZ) (inputsZ W AZ N) j)) :
    (∀ c ∈ naturalLineLc q K W N AZ, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt)) ∧
    (∀ c ∈ naturalLineUc q K W N AZ, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt)) ∧
    (∀ x ∈ naturalLineRcs q K W N AZ, Fits w (⟨x,0⟩ : GaussianInt)) := by
  have hfac := factorRowsZ_facState q K (inputsZ W AZ N) (windowZ W AZ)
  have hlen : (inputsZ W AZ N).length = N := by simp [inputsZ]
  rw [hlen] at hfac
  have hupper : ∀ row ∈ (factorRowsZ q K (windowZ W AZ) (inputsZ W AZ N)).map Prod.snd,
      ∀ x ∈ row, Fits w (⟨x,0⟩ : GaussianInt) := by
    intro row hr
    rw [hfac,List.map_map] at hr
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
    exact (FacFits.tables (hfit j (List.mem_range.mp hj))).2.1
  refine ⟨?_,?_,?_⟩
  · intro c hc
    rw [naturalLineLc,hfac,List.map_map] at hc
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
    exact (FacFits.tables (hfit j (List.mem_range.mp hj))).1
  · intro c hc x hx
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
    split_ifs
    · apply integer_getD_fits
      intro y hy
      by_cases hi : m-d < ((factorRowsZ q K (windowZ W AZ) (inputsZ W AZ N)).map Prod.snd).length
      · rw [List.getD_eq_getElem _ _ hi] at hy
        exact hupper _ (List.getElem_mem _) y hy
      · rw [List.getD_eq_default _ _ (by omega)] at hy
        simp at hy
    · constructor <;> simp
  · rw [naturalLineRcs,hfac,List.map_map]
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    exact (FacFits.tables (hfit j (List.mem_range.mp hj))).2.2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

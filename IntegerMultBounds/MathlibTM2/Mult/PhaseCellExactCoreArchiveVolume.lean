module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows

/-! Certified row shapes determine physical archive volume independently of
numerical witnesses and of forward/reverse core storage order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem ExactCoreRows.word_length {p W width k : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    {rows : List (List GaussianInt)} (h : ExactCoreRows (A := A) p W width k Fs J rows) :
    (cstream A W rows.flatten).length = Fs.length*(coreLength s width k*W) := by
  rw [length_cstream,length_flatten_const rows h.2.1,h.1,Nat.mul_assoc]

theorem exactCoreOutputs_volume {p W width L : ℕ}
    (ks : List ℕ) (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (outputs : List (List (Fin (A+4))))
    (h : ∃ batches, outputs = batches.map (fun rows => cstream A W rows.flatten) ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W width k Fs J rows) ks batches)
    (hcore : ∀ k ∈ ks, coreLength s width k = L) :
    outputs.reverse.flatten.length = ks.length*(Fs.length*(L*W)) := by
  obtain ⟨batches,rfl,hrows⟩ := h
  have hlength : ∀ rows ∈ batches, (cstream A W rows.flatten).length = Fs.length*(L*W) := by
    induction hrows with
    | nil => simp
    | @cons k rows ks batches hk ht ih =>
      intro rs hrs
      rcases List.mem_cons.mp hrs with rfl | hrs
      · rw [hk.word_length,hcore k (by simp)]
      · exact ih (fun j hj => hcore j (by simp [hj])) rs hrs
  rw [length_flatten_const _ (by
    intro word hw
    obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hw)
    exact hlength rows hr),List.length_reverse,List.length_map,←hrows.length_eq]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

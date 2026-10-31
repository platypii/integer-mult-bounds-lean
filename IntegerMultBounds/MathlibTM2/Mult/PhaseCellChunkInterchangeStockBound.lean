module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeLoopStock

/-! Common rectangular volume pays every stage reserve, independently of the
number of chronological stages. The selected supplier coefficient stays sealed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

noncomputable def chunkStockCoefficient (T : ℕ) : ℕ :=
  2*T*M8.Machine.BinaryInterchangeRunWithin.coefficient+5*T+342

private theorem fields_le_volume {P B d V : ℕ} (hP : 0 < P) (hB : 0 < B)
    (hV : V = BinaryAdjacentWidthInterchange.volume P (2^d) 1 (2^d) B) :
    P ≤ V ∧ B ≤ V ∧ d ≤ V := by
  have hK : 0 < 2^d := pow_pos (by decide) _
  have h₁ := Nat.le_mul_of_pos_right P hK
  have h₂ := Nat.le_mul_of_pos_right (P*2^d) hK
  have h₃ : P*2^d*2^d ≤ V := by
    rw [hV]
    simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using
      Nat.le_mul_of_pos_right (P*2^d*2^d) hB
  have h₄ : B ≤ V := by
    rw [hV]
    simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using
      Nat.le_mul_of_pos_left B (Nat.mul_pos (Nat.mul_pos hP hK) hK)
  have h₅ := Nat.le_mul_of_pos_left (2^d) hP
  exact ⟨h₁.trans (h₂.trans h₃),h₄,
    (Nat.lt_two_pow_self (n := d)).le.trans (h₅.trans (h₂.trans h₃))⟩

private theorem linear_stage (T C P B d V : ℕ) (hP : P ≤ V) (hB : B ≤ V)
    (hd : d ≤ V) (hV : 0 < V) :
    2*(21*(P+1+B+d+d)+56)+T*(2*(C*V)+2)+3*T+20 ≤
      (2*T*C+5*T+342)*V := by
  have hTV : T ≤ T*V := Nat.le_mul_of_pos_right T hV
  nlinarith

theorem chunkStageStockAllowance_le {T d V : ℕ} (r : ChunkInterchangeStage T)
    (hP : 0 < r.outerCount) (hB : 0 < r.blockWidth)
    (hV : V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth) :
    chunkStageStockAllowance T d r ≤ chunkStockCoefficient T*V := by
  obtain ⟨hP',hB',hd⟩ := fields_le_volume hP hB hV
  dsimp only [chunkStageStockAllowance,SwapMachineStock.reserve,chunkStockCoefficient]
  rw [←hV]
  exact linear_stage _ _ _ _ _ _ hP' hB' hd (hP.trans_le hP')

theorem chunkStockAllowance_le {T : ℕ} (d V : ℕ) (rs : List (ChunkInterchangeStage T))
    (hpositive : ∀ r ∈ rs, 0 < r.outerCount ∧ 0 < r.blockWidth)
    (hvolume : ∀ r ∈ rs,
      V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth) :
    chunkStockAllowance T d rs ≤ chunkStockCoefficient T*V := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    apply max_le
    · exact chunkStageStockAllowance_le r (hpositive r (by simp)).1 (hpositive r (by simp)).2
        (hvolume r (by simp))
    · exact ih (by intro s hs; exact hpositive s (by simp [hs]))
        (by intro s hs; exact hvolume s (by simp [hs]))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

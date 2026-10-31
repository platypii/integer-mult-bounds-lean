module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
public import IntegerMultBounds.Machine.SharedBankRawComposeWithin
public import IntegerMultBounds.Machine.SharedBankFamily
public import IntegerMultBounds.Machine.HoareHeadChange

/-! Bounded clean blocks compose physically; their actual endpoint travel
transfers margins between differently padded raw banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks
open IntegerMultBounds.Machine
open GraphContract (Runs)
open SharedBankStageInput (raw)
noncomputable section
variable {t a B C : ℕ} {s r : Graph.Block t a} {x y z : Tapes t a} {lo hi : ℤ}

theorem seq_within (hs : Leading s) (hr : Leading r)
    (h₁ : HoareWithin s.program (· = raw x s.tapes) (· = raw y s.tapes) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (h₂ : HoareWithin r.program (· = raw y r.tapes) (· = raw z r.tapes) C
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    HoareWithin (seqB s r).program (· = raw x (seqB s r).tapes) (· = raw z (seqB s r).tapes)
      (B+C+1) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) :=
  SharedBankRawCompose.realizes_within s r lo hi hs hr x y z B C h₁ h₂ hlo hhi

theorem raw_head_change (h : Runs s x y B) :
    ∀ n j, (raw x n).head j-(B : ℕ) ≤ (raw y n).head j ∧
      (raw y n).head j ≤ (raw x n).head j+(B : ℕ) := by
  intro n j
  by_cases hj : j.val < t
  · have ht := h.head_change ⟨j.val,lt_of_lt_of_le hj (SharedBankFamily.common_le s)⟩
    simpa only [raw,hj,↓reduceDIte] using ht
  · simp only [raw,hj,↓reduceDIte]
    constructor <;> omega

/-- Exact restored output bounds extend over every blank private padding. -/
theorem post_raw_heads
    (h : HoareWithin s.program (· = raw x s.tapes) (· = raw y s.tapes) B
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    ∀ n j, lo ≤ (raw y n).head j ∧ (raw y n).head j ≤ hi := by
  obtain ⟨l,hl,c,hr,hh,hp⟩ := h _ rfl
  have hf := hr.finish
  rw [hp] at hf
  intro n j
  by_cases hj : j.val < t
  · have ht := hf ⟨j.val,lt_of_lt_of_le hj (SharedBankFamily.common_le s)⟩
    simpa only [raw,hj,↓reduceDIte] using ht
  · simpa only [raw,hj,↓reduceDIte] using And.intro hlo hhi

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks

module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationControls

/-! Erase each generated control tape once after all replicas have used it. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem publicationControls_length_le (s width w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w) :
    (gatherControls A ((corePublicationWindows s width width hw).gaps w)).length+
      (gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w)).length ≤ 2*s*w+1 := by
  rw [corePublication_full_gaps,gatherControls_replicate_zero,List.length_replicate,
    corePublication_remainder_gaps]
  have hq := Nat.div_le_self s width
  have hvol := Nat.mul_le_mul_right w (Nat.div_mul_le_self s width)
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw1
  split_ifs <;> simp only [gatherControls,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,Nat.add_zero] <;> nlinarith only [hq,hvol,hsw]

theorem releasePublicationControls_exec (fullControl clippedControl : Fin T)
    (hne : fullControl ≠ clippedControl) (s width w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (v : HS T Q A U) (S : Stacks T A)
    (hfull : S.R fullControl = gatherControls A ((corePublicationWindows s width width hw).gaps w))
    (hclipped : S.R clippedControl = gatherControls A ((corePublicationWindows s width (s%width) hw).gaps w)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 4*s*w+7 ∧
      Exec body (clearWords [fullControl,clippedControl]) (mk v S) n
        (mk v' {S with R := fun i => if i ∈ [fullControl,clippedControl] then [] else S.R i}) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [fullControl,clippedControl] (by simp [hne]) v S
  refine ⟨v',_,hu,?_,he⟩
  have hh := publicationControls_length_le (A := A) s width w hw hw1
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    hfull,hclipped,Nat.add_zero] at *
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

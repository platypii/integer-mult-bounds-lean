module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOriginAdvances
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledBoundaryPublish

/-! Generate all publication controls from coordinates and retire them after publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def generatedBoundaryPublish : Pr P 224 Q A U :=
  .seq generateBoundaryAdvances (.seq controlledBoundaryPublish (uclear 206))

theorem generatedBoundaryPublish_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (V w : ℕ) (hw : 1 ≤ w) (hsV : s ≤ 2^V)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (coordinateTail sourceTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 97).length = s) (hwidth : (S.R 160).length = w) (hV : (S.R 115).length = V)
    (hc : S.R 116 = List.replicate B.card tick)
    (hcoords : S.R 109 = cstream A V ((bOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))++coordinateTail)
    (hsrc : S.R 204 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,184,217,223,201,208,211,215,220,206] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generateBoundaryAdvancesCost B.card V w s+93*s*w+45 ∧
      Exec body generatedBoundaryPublish (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          109 coordinateTail) 204 sourceTail) 132 (cstream A w (chirpLine s G)++S.R 132))}) := by
  let advances := gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])
  let S₁ : Stacks 224 A := {S with R := Function.update (Function.update S.R 109 coordinateTail) 206 advances}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryOriginAdvances_exec (body := body) hA s B V w hsV coordinateTail v S
    hc hV hwidth hcoords (fun i hi => hclean i (List.mem_append_left [184,217,223,201,208,211,215,220,206] hi))
  have he₁' : Exec body generateBoundaryAdvances (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,advances,hclean 206 (by simp)] using he₁
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have ho : i ≠ 109 ∧ i ≠ 206 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,ho.1,ho.2] using hclean i (List.mem_append_right [0,1,2,3,4,5,6,7,8,9] (List.mem_append_left [206] hi))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := controlledBoundaryPublish_exec (body := body) s B w hw G hoff sourceTail [] v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hwidth) (by simpa [S₁] using hc)
    (by simp [S₁,advances]) (by simpa [S₁] using hsrc) hz
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update S₁.R 204 sourceTail) 132
    (cstream A w (chirpLine s G)++S.R 132))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 206 v₂ S₂
  have he₃' : Exec body (uclear 206) (mk v₂ S₂) (2*advances.length+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 206 []}) := by simpa [S₂,S₁] using he₃
  have hlen : advances.length ≤ 2*(s*w)+1 := by
    have hv := boundaryOriginAdvances_volume s B w
    have hB : B.card ≤ s*w := by
      have hh := boundaryScatterGaps_volume s B w
      have hn : B.card ≤ B.card*w := by simpa using Nat.mul_le_mul_left B.card hw
      omega
    simp only [advances,length_gatherControls,List.sum_append,List.sum_singleton,Nat.add_zero,
      List.length_append,List.length_singleton,originAdvances_length]
    have hN : (boundaryScatterOrigins s B).length = B.card := by simp [boundaryScatterOrigins,bOrder_length]
    rw [hN]
    omega
  refine ⟨v₃,n₁+(n₂+(2*advances.length+2)),hu₃.trans (hu₂.trans hu₁),
    by nlinarith only [hn₁,hn₂,hlen],(Exec.seq he₁' (Exec.seq he₂ he₃')).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h109 : i = 109 <;> by_cases h204 : i = 204 <;> by_cases h132 : i = 132 <;>
    by_cases h206 : i = 206 <;> simp [S₂,S₁,h109,h204,h132,h206,hclean 206 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

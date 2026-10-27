module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateBoundaryAdvances
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScatterData

/-! Generate publication advances from the actual ascending boundary coordinate page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem boundaryCoordinatePackets (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (A V : ℕ) :
    (boundaryScatterOrigins s B).flatMap (fun x => tblPairs A V x 0) =
      cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := by
  simp [boundaryScatterOrigins,cstream,List.flatMap_map,csyms,red,tblPairs]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundaryOriginAdvances_exec (hA : 4 ≤ A) (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (V w : ℕ) (hsV : s ≤ 2^V) (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hcount : S.R 116 = List.replicate B.card tick)
    (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hsrc : S.R 109 = cstream A V ((bOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))++tail)
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateBoundaryAdvancesCost B.card V w s ∧
      Exec body generateBoundaryAdvances (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 109 tail) 206
          (gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++S.R 206))}) := by
  have hsorted : (0::boundaryScatterOrigins s B).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp,(boundaryScatterOrigins_disjoint s B).imp (fun h => by omega)⟩
  have hb : ∀ x ∈ boundaryScatterOrigins s B, x ≤ s ∧ x < 2^V := by
    intro x hx
    have h := boundaryScatterOrigins_fit s B x hx
    omega
  obtain ⟨v',n,hu,hn,he⟩ := generateBoundaryAdvances_exec (body := body) hA V w s
    (boundaryScatterOrigins s B) hsorted hb tail v S
    (by simpa [boundaryScatterOrigins,bOrder_length] using hcount) hV hw
    (by rw [boundaryCoordinatePackets]; exact hsrc) hclean
  exact ⟨v',n,hu,by simpa [boundaryScatterOrigins,bOrder_length] using hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

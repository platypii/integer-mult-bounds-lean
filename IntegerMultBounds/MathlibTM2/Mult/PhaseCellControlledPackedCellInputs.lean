module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedLocalAdvanceControls

/-! Actual control generation precedes the bounded local RHS sweep. The source,
origin packets, batch count, ambient headers and all temporary controls survive
or are released exactly as required by the existing arithmetic caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def controlledPackedCellInputs : Pr P 168 Q A U :=
  .seq placedLocalAdvanceControls gatherPackedCellInputs

theorem controlledPackedCellInputs_exec {V N L w s origin : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hNV : N < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hwidth : (S.R 94).length = w) (hrows : (S.R 102).length = L)
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hwV : w < 2^V) (hcoords : origin+N < 2^V) (hunits : (origin+N)*w < 2^V)
    (cs originTail : List (Fin (A+4))) (hcount : S.R 116 = cs) (hlen : cs.length = offsets.length)
    (hpackets : S.R 109 = (offsets.map (origin+·)).flatMap (binSyms V)++originTail)
    (hV : (S.R 163).length = V) (h153 : S.R 153 = binSyms V w)
    (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0)
    (hsmall : ∀ k : Fin 168, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ offsets.length*(3*tblC V V+29*V+30)+8*N*w+78*V+91+
        (offsets.length*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60) ∧
      Exec body controlledPackedCellInputs (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedLocalAdvanceControls_exec (body := body) V origin N w
    hwV hcoords hunits offsets hne hordered
    (fun j hj => (Nat.le_add_right j L).trans (hfit j hj)) cs originTail hlen v S
    hV h153 h155 h154 hcount hpackets hsmall
    (hfresh 88 (by simp)) (hfresh 89 (by simp)) (hfresh 90 (by simp)) (hfresh 91 (by simp))
  let G : Stacks 168 A := {S with R := (Function.update S.R 91
    (match offsets.map (·*w) with | [] => [] | j::js => gatherControls A (j::windowAdvances j js)))}
  have hclean : ∀ k ∈ [(0 : Fin 168),1,2,3,4,5,6,7,8,9,92,104,105,108], G.R k = [] := by
    intro k hk
    have hne91 : k ≠ 91 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hin : k.val < 19 ∨ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | (left; decide) | (right; simp)
    have hz : S.R k = [] := hin.elim (hsmall k) (hfresh k)
    simpa [G,hne91] using hz
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := gatherPackedCellInputs_exec (body := body)
    C hhalo hNV offsets hne hordered hfit tail v₁ G
    (by simpa [G] using h165) (by simpa [G] using h166)
    (by simpa [G] using hwidth) (by simpa [G] using hrows)
    (by simpa [G] using hsource) (by cases hm : offsets.map (·*w) <;> simp [G,hm]) hclean
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h91 : k = 91 <;> by_cases h110 : k = 110 <;>
    simp [G,h91,h110,hfresh 91 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

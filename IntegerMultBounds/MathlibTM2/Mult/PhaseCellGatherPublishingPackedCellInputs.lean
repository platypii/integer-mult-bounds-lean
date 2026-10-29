module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPackedCellInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublicationFromDimensions

/-! Use one advance schedule for input gathering and later publication. Protected
publication controls survive the gather; no origin packet is evaluated twice. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def gatherPublishingPackedCellInputs : Pr P 168 Q A U :=
  .seq packedCellPublicationFromDimensions gatherPackedCellInputs

theorem gatherPublishingPackedCellInputs_exec {V N L w s origin : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hNV : N < 2^V)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hwidth : (S.R 94).length = w) (hrows : (S.R 102).length = L)
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hcontrol : S.R 91 = gatherControls A (originAdvances w 0 offsets++[0]))
    (hcount : S.R 116 = List.replicate offsets.length tick)
    (hpublication : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], S.R k = [])
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,3,4,5,6,7,8,9,92,104,105,108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (12*N*w+21*offsets.length+6*L*w+9*L+27)+
        (offsets.length*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60) ∧
      Exec body gatherPublishingPackedCellInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 140
          (gatherControls A (packedCellGaps L w offsets)++S.R 140)) 110
          (offsets.flatMap (fun j => cstream A w (packedInterval (origin+j) L C))++S.R 110)) 91 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedCellPublicationFromDimensions_exec (body := body)
    N L w offsets hne hdis hfit [] v S hrows hwidth hcount
    (by simpa using hcontrol) hpublication
  let G : Stacks 168 A := {S with R := (Function.update S.R 140
    (gatherControls A (packedCellGaps L w offsets)++S.R 140))}
  have hcleanG : ∀ k ∈ [(0 : Fin 168),1,2,3,4,5,6,7,8,9,92,104,105,108], G.R k = [] := by
    intro k hk
    have hn : k ≠ 140 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [G,hn] using hclean k hk
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := gatherPackedCellInputs_exec (body := body)
    C hhalo hNV offsets hne (hdis.imp (fun h => by omega)) hfit tail v₁ G
    (by simpa [G] using h165) (by simpa [G] using h166)
    (by simpa [G] using hwidth) (by simpa [G] using hrows)
    (by simpa [G] using hsource)
    (by simpa [G,hcontrol] using (packedGatherControls_eq (A := A) w 0 offsets hne)) hcleanG
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

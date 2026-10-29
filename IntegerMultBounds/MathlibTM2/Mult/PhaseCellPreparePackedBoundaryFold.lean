module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMoveCountedLine

/-! Derive the boundary count, isolate its ordered RHS prefix, and generate the
existing fold controls. The borrowed RHS suffix and all shared data survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def preparePackedBoundaryFold : Pr P 168 Q A U :=
  .seq packedBoundaryCount (.seq (ScalarPlacement.moveCountedLine 116 130 93 143 4 0 1 2)
    packedBoundaryFoldCounters)

def preparePackedBoundaryFoldCost (N n w : ℕ) : ℕ :=
  7*N+4+ScalarPlacement.moveCountedLineCost n w+boundaryFoldCountersCost n w

def packedBoundaryFoldInputR (n w : ℕ) (words tail : List (Fin (A+4))) (R : Regs 168 A) : Regs 168 A :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update R
    116 (List.replicate n tick)) 93 tail) 143 words) 0 (List.replicate (n/2) tick))
    2 (List.replicate ((n+1)/2-n/2) tick)) 3 (List.replicate (((n+1)/2)*w) tick)

theorem preparePackedBoundaryFold_exec {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hsrc : S.R 93 = cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++tail)
    (hw : (S.R 130).length = w) (hblank : ∀ k : Fin 168, k.val < 6 → S.R k = [])
    (h116 : S.R 116 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparePackedBoundaryFoldCost N (haloBoundary s t band a b).card w ∧
      Exec body preparePackedBoundaryFold (mk v S) m
        (mk v' {S with R := (packedBoundaryFoldInputR (haloBoundary s t band a b).card w
          (cstream A w ((bOrder s (haloBoundary s t band a b)).map C)) tail S.R)}) := by
  let B := haloBoundary s t band a b
  let words := cstream A w ((bOrder s B).map C)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedBoundaryCount_exec (body := body) hst hA band a b hb hfit hB
    v S hmask (hblank 0 (by decide)) h116
  let S₁ : Stacks 168 A := {S with R := Function.update S.R 116 (List.replicate B.card tick)}
  have hlen : words.length = B.card*w := by
    have hbOrder : (bOrder s B).length = B.card := by
      rw [← List.toFinset_card_of_nodup (bOrder_nodup s B),bOrder_toFinset]
    simp only [words,length_cstream,List.length_map,hbOrder]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := ScalarPlacement.moveCountedLine_exec (body := body)
    116 130 93 143 4 0 1 2 (by decide) B.card w words tail hlen v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hw) (by simpa [S₁] using hsrc)
    (by simpa [S₁] using hblank 4 (by decide)) (by simpa [S₁] using hblank 0 (by decide))
    (by simpa [S₁] using hblank 1 (by decide)) (by simpa [S₁] using hblank 2 (by decide))
  let S₂ : Stacks 168 A := {S₁ with R := (Function.update (Function.update S₁.R 93 tail) 143 words)}
  have he₂' : Exec body (ScalarPlacement.moveCountedLine 116 130 93 143 4 0 1 2)
      (mk v₁ S₁) m₂ (mk v₂ S₂) := by simpa [S₁,h143] using he₂
  have hblank₂ : ∀ k : Fin 168, k.val < 6 → S₂.R k = [] := by
    intro k hk
    have hn (j : Fin 168) (hj : 6 ≤ j.val) : k ≠ j := by
      intro he; have hh := congrArg Fin.val he; omega
    simpa [S₂,S₁,hn 93 (by decide),hn 143 (by decide),hn 116 (by decide)] using hblank k hk
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := packedBoundaryFoldCounters_exec (body := body) B.card w v₂ S₂
    (by simp [S₂,S₁]) (by simpa [S₂,S₁] using hw) hblank₂
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_⟩
  · dsimp only [preparePackedBoundaryFoldCost]
    change m₁+(m₂+m₃) ≤ 7*N+4+ScalarPlacement.moveCountedLineCost B.card w+boundaryFoldCountersCost B.card w
    omega
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

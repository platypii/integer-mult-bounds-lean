module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate all retained fold counters and the boundary-symbol volume once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

def replicaBoundaryCounters : Pr P 242 Q A U :=
  .seq replicaBoundaryFoldCounters (unaryProduct 116 130 124 104 105)

def replicaBoundaryCounterState (n w : ℕ) (S : Stacks 242 A) : Stacks 242 A :=
  let K := replicaBoundaryFoldCounterState n w S
  {K with R := Function.update K.R 124 (List.replicate (n*w) tick)}

def replicaBoundaryCountersCost (n w : ℕ) := boundaryFoldCountersCost n w+n*(4*w+9)+4

theorem replicaBoundaryCounters_exec (n w : ℕ) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hn : (S.R 116).length = n) (hw : (S.R 130).length = w)
    (hblank : ∀ k ∈ [(1 : Fin 242),4,5,104,105,117,118,120,124], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicaBoundaryCountersCost n w ∧
      Exec body replicaBoundaryCounters (mk v S) m (mk v' (replicaBoundaryCounterState n w S)) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := replicaBoundaryFoldCounters_exec (body := body) n w v S hn hw (by
    intro k hk
    exact hblank k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let K := replicaBoundaryFoldCounterState n w S
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := 116) (b := 130) (dst := 124) (t₁ := 104) (t₂ := 105) (by decide) v₁ K
    (by simpa [K,replicaBoundaryFoldCounterState] using hblank 104 (by simp))
    (by simpa [K,replicaBoundaryFoldCounterState] using hblank 105 (by simp))
  have hnK : (K.R 116).length = n := by simpa [K,replicaBoundaryFoldCounterState] using hn
  have hwK : (K.R 130).length = w := by simpa [K,replicaBoundaryFoldCounterState] using hw
  have h124 : K.R 124 = [] := by simpa [K,replicaBoundaryFoldCounterState] using hblank 124 (by simp)
  have he₂' : Exec body (unaryProduct 116 130 124 104 105) (mk v₁ K) m₂
      (mk v₂ (replicaBoundaryCounterState n w S)) := by
    simpa only [hnK,hwK,h124,List.append_nil,replicaBoundaryCounterState] using he₂
  have hm₂' : m₂ ≤ n*(4*w+9)+4 := by simpa only [hnK,hwK] using hm₂
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,by unfold replicaBoundaryCountersCost; omega,Exec.seq he₁ he₂'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

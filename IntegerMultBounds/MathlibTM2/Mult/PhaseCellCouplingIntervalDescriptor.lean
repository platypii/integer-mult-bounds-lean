module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Binary origin/length packets enter and leave the local coupling workspace.
Shared geometry survives every step of the interval traversal. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def loadCouplingIntervalDescriptor : Pr P 168 Q A U :=
  .seq (takePrefix 163 159 155 0 1) (takePrefix 163 159 165 0 1)

theorem loadCouplingIntervalDescriptor_exec (V origin N : ℕ)
    (tail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hV : (S.R 163).length = V)
    (hsrc : S.R 159 = binSyms V origin++binSyms V N++tail)
    (h155 : S.R 155 = []) (h165 : S.R 165 = []) (h0 : S.R 0 = []) (h1 : S.R 1 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body loadCouplingIntervalDescriptor (mk v S) (12*V+12)
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 159 tail)
          155 (binSyms V origin)) 165 (binSyms V N))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (count := 163) (src := 159) (dst := 155) (buf := 0) (tmp := 1) (by decide)
    v S (binSyms V origin) (binSyms V N++tail)
    (by simpa only [List.append_assoc] using hsrc) (by simpa using hV) h0 h1
  let B : Stacks 168 A := {S with R := (Function.update (Function.update S.R 159
    (binSyms V N++tail)) 155 (binSyms V origin))}
  have he₁' : Exec body (takePrefix 163 159 155 0 1) (mk v S) (6*V+6) (mk v₁ B) := by
    simpa [B,h155] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (count := 163) (src := 159) (dst := 165) (buf := 0) (tmp := 1) (by decide)
    v₁ B (binSyms V N) tail (by simp [B]) (by simpa [B] using hV)
    (by simpa [B] using h0) (by simpa [B] using h1)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast (by simp; omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h159 : k = 159 <;> by_cases h155' : k = 155 <;> by_cases h165' : k = 165 <;>
    simp [B,h159,h155',h165',h165]

def releaseCouplingIntervalDescriptor : Pr P 168 Q A U :=
  clearWords [148,154,155,156,164,165]

theorem releaseCouplingIntervalDescriptor_exec (V : ℕ)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hfields : ∀ k ∈ [(148 : Fin 168),154,155,156,164,165], (S.R k).length = V) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseCouplingIntervalDescriptor (mk v S) (12*V+13)
        (mk v' {S with R := fun k => if k ∈ [(148 : Fin 168),154,155,156,164,165] then [] else S.R k}) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(148 : Fin 168),154,155,156,164,165]
    (by decide) v S
  have hsum : ([(148 : Fin 168),154,155,156,164,165].map (fun k => (S.R k).length)).sum = 6*V := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [hfields 148 (by simp),hfields 154 (by simp),hfields 155 (by simp),
      hfields 156 (by simp),hfields 164 (by simp),hfields 165 (by simp)]
    omega
  exact ⟨v',hu,he.cast (by rw [hsum]; simp; omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

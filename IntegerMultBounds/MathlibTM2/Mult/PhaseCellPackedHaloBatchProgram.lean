module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInputExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type}

def packedHaloBatchReg : Fin 248 → Fin 249 := Fin.castLE (by decide)

noncomputable def packedHaloBatchStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  let step : Pr P 248 Q A U := .seq packedFreshOutput (packedHaloPreparedInput hR hQ)
  embProg packedHaloBatchReg id step

/-- One fixed program; only the unary counter varies with the replica count. -/
noncomputable def packedHaloBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  countedLoop 248 (packedHaloBatchStep hR hQ)

def packedHaloBatchCost (replicas perInput : ℕ) : ℕ := replicas*(perInput+3)+2

/-- Lift the checked numerical step while preserving the external loop counter. -/
theorem packedHaloBatchStep_exec {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {v v' : HS 248 Q A U} {S F : Stacks 248 A} {n : ℕ}
    (he : Exec body (.seq (packedFreshOutput (P := P) (U := U)) (packedHaloPreparedInput (P := P) (U := U) hR hQ)) (mk v S) n (mk v' F))
    (v₀ : HS 249 Q A U) (S₀ : Stacks 249 A)
    (hv : embDn packedHaloBatchReg v₀ = v) (hS : embStk packedHaloBatchReg S₀ = S) :
    ∃ v₁ F₁, v₁.user = v'.user ∧
      Exec body' (packedHaloBatchStep hR hQ) (mk v₀ S₀) n (mk v₁ F₁) ∧
      embStk packedHaloBatchReg F₁ = F ∧
      F₁.L 248 = S₀.L 248 ∧ F₁.R 248 = S₀.R 248 := by
  have hinj : Function.Injective packedHaloBatchReg := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 249 => k.val) hij)
  obtain ⟨v₁,F₁,hex,hv₁,hu₁,hview,hframe⟩ := exec_emb hinj hbody he v₀ hv S₀ hS
  have hcounter := hframe 248 (by
    intro i heq
    have hv := congrArg Fin.val heq
    have hi := i.isLt
    change i.val = 248 at hv
    omega)
  exact ⟨v₁,F₁,hu₁,hex,hview,hcounter⟩

/-- Scheduling bridge for a structural numerical invariant on the solver bank.
The concrete one-input execution discharges `hstep`; the loop itself only
consumes its isolated counter and pays three control steps per input. -/
theorem packedHaloBatch_exec {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (N cost : ℕ)
    (Inv : ℕ → Stacks 248 A → Prop)
    (hstep : ∀ j < N, ∀ (v : HS 248 Q A U) S, Inv j S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
        Exec body (.seq packedFreshOutput (packedHaloPreparedInput hR hQ)) (mk v S) n (mk v' F) ∧ Inv (j+1) F)
    (v : HS 249 Q A U) (S : Stacks 249 A) (hcount : (S.R 248).length = N)
    (hInv : Inv 0 (embStk packedHaloBatchReg S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ packedHaloBatchCost N cost ∧
      Exec body' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧ Inv N (embStk packedHaloBatchReg F) := by
  apply countedLoop_exec 248 (packedHaloBatchStep hR hQ) N cost
    (fun j S => Inv j (embStk packedHaloBatchReg S)) ?_ ?_ v S hcount hInv
  · intro j S xs hI
    have hview : embStk packedHaloBatchReg {S with R := Function.update S.R 248 xs} =
        embStk packedHaloBatchReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      have hne : packedHaloBatchReg i ≠ 248 := by
        intro he; have hv := congrArg (fun k : Fin 249 => k.val) he
        have hi := i.isLt; change i.val = 248 at hv; omega
      exact Function.update_of_ne hne _ _
    rw [hview]; exact hI
  · intro j hj v S hI
    obtain ⟨v₁,F,n,hu,hn,he,hnext⟩ := hstep j hj (embDn packedHaloBatchReg v)
      (embStk packedHaloBatchReg S) hI
    obtain ⟨v₂,F₂,hu₂,he₂,hview,hleft,hcounter⟩ := packedHaloBatchStep_exec hbody hR hQ he v S rfl rfl
    refine ⟨v₂,F₂,n,hu₂.trans hu,hn,he₂,hcounter,?_⟩
    rw [hview]; exact hnext

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

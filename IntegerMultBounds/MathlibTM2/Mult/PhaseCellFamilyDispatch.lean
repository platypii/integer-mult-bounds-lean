module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! Execute the descriptor schedule and restore its tape, count and private workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem familyDispatch_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} {d : ℝ} (hp : 2 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A)) (hready : ∀ r ∈ records, FamilyDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => (value (r.precision p l t) (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => (value (r.precision p l t) (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.cost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ∧
      Exec body (familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs := by
  obtain ⟨v',n,outputs,hu,hn,he,hgood,_⟩ := familyDispatch_exec_trace (body := body)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA hp hst hθ hgap
    records hready x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  exact ⟨v',n,outputs,hu,hn,he,hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

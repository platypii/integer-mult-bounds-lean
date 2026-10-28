module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchLoopTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! A fixed counted loop executes every advertised numerical descriptor exactly once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem familyDispatchLoop_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock])
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
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.cost p l t work+3)).sum+2 ∧
      Exec body (familyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
        (mk v S) n (mk v' (descriptorLoopFinal work FamilyDispatchInput.words records src saved result clock rest outputs S)) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs := by
  obtain ⟨v',n,outputs,hu,hn,he,hgood,_⟩ := familyDispatchLoop_exec_trace (body := body)
    work hwork src saved count tmp spare result clock hreg hsep recovery hR hQ hA hp hst hθ hgap
    records hready x y hx hy v S rest hblank hleft hscratch hsource hclock
  exact ⟨v',n,outputs,hu,hn,he,hgood⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

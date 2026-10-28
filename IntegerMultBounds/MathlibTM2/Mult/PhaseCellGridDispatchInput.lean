module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedBatchDispatchStep

/-! Execute a p-grid numerical batch inside the generic load, solve and collect lifecycle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance

namespace FamilyDispatchInput
variable {s A : ℕ} [NeZero s]

noncomputable def gridCost {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+
    gridFamilyInverseBatchCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*(2*p+13))+2*(∑ i, (r.words i).length)+611)

noncomputable def gridStock {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+
    gridFamilyInverseBatchStockCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*(2*p+13))+2*(∑ i, (r.words i).length)+611)

end FamilyDispatchInput

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def gridFamilyInverseBatchDispatchStep (work : Fin 303 → Fin T)
    (src saved count tmp spare result : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  descriptorSolverStep work src saved count tmp spare result (gridFamilyInverseBatch (P := Empty) recovery hR hQ)

theorem gridDispatchInput_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hresult : result ∉ [src,saved,count,tmp,spare]) (hresultWork : ∀ i, work i ≠ result)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} {d : ℝ} (hp : 2 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : GridDispatchReady p l t d r)
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (x F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work r.words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n Zs, v'.user = v.user ∧ n ≤ r.gridCost p l t work ∧
      Exec body (gridFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
        (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.normalizedOutput p Zs) S)) ∧
      NormalizedDispatchApprox p r x y Zs ∧
      ∀ C, mnProgPush (gridFamilyInverseBatchDispatchStep work src saved count tmp spare result
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*r.gridStock p l t work)
          depth (gridFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
          (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.normalizedOutput p Zs) S)) := by
  let post := fun output => ∃ Zs : List (ZMod s → GaussianInt),
    output = r.normalizedOutput p Zs ∧ NormalizedDispatchApprox p r x y Zs
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr.uPositive)
  have hsolve : ∀ vi : HS 303 Q A U, ∃ vf n output, vf.user = vi.user ∧
      n ≤ gridFamilyInverseBatchCost A (inverseCallerWordWidth p r.u l r.target s t)
        p r.u l s t r.a r.b r.target r.inputs.length ∧
      Exec (fun f : Empty => nomatch f) (gridFamilyInverseBatch recovery hR hQ)
        (mk vi (descriptorReadyBank work r.words S)) n
        (mk vf {descriptorReadyBank work r.words S with R :=
          (Function.update (descriptorReadyBank work r.words S).R 132 output)}) ∧ post output ∧
      ∀ C, mnProgPush (gridFamilyInverseBatch (P := Empty) (U := U) (A := A) recovery hR hQ) ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f) (fun d z => mnSize z+d ≤
          mnSize (mk vi (descriptorReadyBank work r.words S))+depth+
          (C+1)*gridFamilyInverseBatchStockCost A (inverseCallerWordWidth p r.u l r.target s t)
            p r.u l s t r.a r.b r.target r.inputs.length) depth (gridFamilyInverseBatch recovery hR hQ)
          (mk vi (descriptorReadyBank work r.words S)) n
          (mk vf {descriptorReadyBank work r.words S with R :=
            (Function.update (descriptorReadyBank work r.words S).R 132 output)}) := by
    intro vi
    obtain ⟨vf,n,Zs,hu,hn,he,ha,ht⟩ := gridFamilyInverseBatch_spec (body := fun f : Empty => nomatch f)
      recovery hR hQ hA hp hr.width hα hst hr.uPositive hαu hθ hgap (by rw [hαu]; exact hr.budget)
      hr.band hr.a hr.b hr.padding r.inputs hr.inputBound vi (descriptorReadyBank work r.words S)
      r.scalarWidth hr.scalarWidth hr.scalars hleft hr.blank hr.source hr.count hr.outputBlank x y hx hy
    refine ⟨vf,n,_,hu,hn,he,⟨Zs,rfl,?_⟩,?_⟩
    · exact ha
    · intro C hc depth
      exact ht C hc (fun f => nomatch f) depth
  obtain ⟨v',n,output,hu,hn,he,⟨Zs,hZ,ha⟩,ht⟩ := descriptorSolverStep_exec (body := body)
    work hwork src saved count tmp spare result hreg hresult hresultWork hsep r.words rest
    (gridFamilyInverseBatch (P := Empty) recovery hR hQ)
    (gridFamilyInverseBatchCost A (inverseCallerWordWidth p r.u l r.target s t) p r.u l s t r.a r.b r.target r.inputs.length)
    (gridFamilyInverseBatchStockCost A (inverseCallerWordWidth p r.u l r.target s t) p r.u l s t r.a r.b r.target r.inputs.length)
    (r.inputs.length*s*(2*p+13)) post v S hblank hsource hcount htmp hspare hsolve (by
      intro output hp
      obtain ⟨Zs,rfl,ha⟩ := hp
      have hlen : Zs.length = r.inputs.length := ha.length_eq.symm
      simp only [FamilyDispatchInput.normalizedOutput,familyBatchWords_length,hlen]
      exact le_rfl)
  subst output
  exact ⟨v',n,Zs,hu,hn,he,ha,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

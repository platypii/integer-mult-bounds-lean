module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedBatchDispatchStep

/-! The normalized step uses the same ordinary descriptor records and readiness contract. -/

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

noncomputable def normalizationCost (p l t : ℕ) (r : FamilyDispatchInput s A) : ℕ :=
  inverseRoundBatchCost (inverseCallerWordWidth p r.u l r.target s t)
    p r.u l r.target s t r.a r.b (r.inputs.length*s)

noncomputable def normalizedCost {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+
    normalizedFamilyInverseBatchCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*(2*p+13))+2*(∑ i, (r.words i).length)+611)

noncomputable def normalizedStock {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+
    normalizedFamilyInverseBatchStockCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*(2*p+13))+2*(∑ i, (r.words i).length)+611)

def normalizedOutput (p : ℕ) (_r : FamilyDispatchInput s A) (Zs : List (ZMod s → GaussianInt)) :=
  cstream A (2*p+13) (Zs.map (chirpLine s)).flatten

end FamilyDispatchInput

def NormalizedDispatchApprox {s A : ℕ} [NeZero s] (p : ℕ) (r : FamilyDispatchInput s A)
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ) (Zs : List (ZMod s → GaussianInt)) : Prop :=
  List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s r.a r.b)
    (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
    (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨x F i,y F i⟩ : ℂ))
    (2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^inverseNormalizationShift p)) r.inputs Zs

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem normalizedDispatchInput_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hresult : result ∉ [src,saved,count,tmp,spare]) (hresultWork : ∀ i, work i ≠ result)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} {d : ℝ} (hp : 2 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : FamilyDispatchReady p l t d r)
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (x F)
      (fun i => (value (r.precision p l t) (F i)).re))
    (hy : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (y F)
      (fun i => (value (r.precision p l t) (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work r.words)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n Zs, v'.user = v.user ∧ n ≤ r.normalizedCost p l t work ∧
      Exec body (normalizedFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
        (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.normalizedOutput p Zs) S)) ∧
      NormalizedDispatchApprox p r x y Zs ∧
      ∀ C, mnProgPush (normalizedFamilyInverseBatchDispatchStep work src saved count tmp spare result
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*r.normalizedStock p l t work)
          depth (normalizedFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
          (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.normalizedOutput p Zs) S)) := by
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr.uPositive)
  obtain ⟨v',n,Zs,hu,hn,he,ha,ht⟩ := normalizedFamilyInverseBatchDispatchStep_spec (body := body)
    work hwork src saved count tmp spare result hreg hresult hresultWork hsep recovery hR hQ hA
    hp hr.width hα hst hr.uPositive hαu hθ hgap (by rw [hαu]; exact hr.budget)
    hr.band hr.a hr.b hr.padding r.inputs hr.inputBound v S [] r.words rest hr.outputBlank
    hblank hsource hcount htmp hspare r.scalarWidth hr.scalarWidth hr.scalars hleft hr.blank
    (by simpa only [List.append_nil,descriptorReadyBank,FamilyDispatchInput.width] using hr.source) hr.count x y hx hy
  refine ⟨v',n,Zs,hu,hn,he,?_,ht⟩
  simpa only [NormalizedDispatchApprox,FamilyDispatchInput.precision,FamilyDispatchInput.width,hr.outputBlank,List.append_nil] using ha

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPhysicalDispatchCost

/-! Ordinary descriptor records and the checked numerical contract of one dispatch step. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance

structure FamilyDispatchInput (s A : ℕ) where
  u : ℕ
  target : ℕ
  a : ℕ
  b : ℕ
  inputs : List (ZMod s → GaussianInt)
  words : Fin 303 → List (Fin (A+4))
  scalarWidth : List (Fin (A+4))

namespace FamilyDispatchInput
variable {s A : ℕ} [NeZero s]

noncomputable def precision (p l t : ℕ) (r : FamilyDispatchInput s A) : ℕ :=
  executionPrecision p l (initialSchurTarget p r.u
    (boundaryTableBits p (boundaryRecoveryTarget p (r.target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p r.u) r.a r.b).card) 2) 2

noncomputable def width (p l t : ℕ) (r : FamilyDispatchInput s A) : ℕ :=
  executionWidth p l (initialSchurTarget p r.u
    (boundaryTableBits p (boundaryRecoveryTarget p (r.target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p r.u) r.a r.b).card) 2) 2

def rawBank (r : FamilyDispatchInput s A) : Stacks 303 A := ⟨[],[],fun _ => [],r.words⟩

noncomputable def cost {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  Cost.physicalFamilyDispatchCost T A (inverseCallerWordWidth p r.u l r.target s t)
    p r.u l s t r.a r.b r.target r.inputs.length work r.words

noncomputable def stock {T : ℕ} (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) : ℕ :=
  takeDescriptorBankCost (placedDescriptorFields work r.words)+
    familyInverseBatchCallerStockCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*r.width p l t)+2*(∑ i, (r.words i).length)+611)

noncomputable def output (p l t : ℕ) (r : FamilyDispatchInput s A) (Zs : List (ZMod s → GaussianInt)) :=
  cstream A (r.width p l t) (Zs.map (chirpLine s)).flatten

end FamilyDispatchInput

structure FamilyDispatchFrame {s A : ℕ} [NeZero s] (p l t : ℕ) (d : ℝ)
    (r : FamilyDispatchInput s A) : Prop where
  uPositive : 1 ≤ r.u
  width : 8*p ≤ 2^r.u
  budget : (r.u : ℝ)*d ≤ p
  band : PhaseCellBand.width p r.u ≤ s
  a : r.a ≤ s
  b : r.b ≤ s
  padding : 2*((s/(t-s)+1)-2*PhaseCellBand.width p r.u) ≤ 2^l+1
  outputBlank : r.words 132 = []
  scalarWidth : r.scalarWidth.length = inverseCallerWordWidth p r.u l r.target s t
  scalars : tblHolds familyInverseScalarReg r.rawBank
    (tblRho (inverseCallerWordWidth p r.u l r.target s t) r.scalarWidth []
      (inverseInputScalars p r.u l r.target s t r.a r.b))
  blank : ∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → r.words (familyInverseCoreReg i) = []
  source : r.words 110 = cstream A (r.width p l t) (r.inputs.map (chirpLine s)).flatten
  count : (r.words (familyInverseCoreReg 246)).length = r.inputs.length

structure FamilyDispatchReady {s A : ℕ} [NeZero s] (p l t : ℕ) (d : ℝ)
    (r : FamilyDispatchInput s A) : Prop extends FamilyDispatchFrame p l t d r where
  inputBound : ∀ F ∈ r.inputs, ∀ i, ‖value (r.precision p l t) (F i)‖ ≤ (2 : ℝ)^2


def FamilyDispatchApprox {s A : ℕ} [NeZero s] (p l t : ℕ) (r : FamilyDispatchInput s A)
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ) (Zs : List (ZMod s → GaussianInt)) : Prop :=
  List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s r.a r.b)
    (pairedCellRead (r.precision p l t) (r.width p l t) (cstream A (r.width p l t) (chirpLine s Z)))
    (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^r.target)) r.inputs Zs

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem familyDispatchInput_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
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
    ∃ v' n Zs, v'.user = v.user ∧ n ≤ r.cost p l t work ∧
      Exec body (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
        (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.output p l t Zs) S)) ∧
      FamilyDispatchApprox p l t r x y Zs ∧
      ∀ C, mnProgPush (familyInverseBatchDispatchStep work src saved count tmp spare result
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*r.stock p l t work)
          depth (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
          (mk v S) n (mk v' (dispatchedDescriptorState work r.words src saved result rest (r.output p l t Zs) S)) := by
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr.uPositive)
  obtain ⟨v',n,Zs,hu,hn,he,ha,ht⟩ := familyInverseBatchDispatchStep_spec (body := body)
    work hwork src saved count tmp spare result hreg hresult hresultWork hsep recovery hR hQ hA
    hp hr.width hα hst hr.uPositive hαu hθ hgap (by rw [hαu]; exact hr.budget)
    hr.band hr.a hr.b hr.padding r.inputs hr.inputBound v S [] r.words rest hr.outputBlank
    hblank hsource hcount htmp hspare r.scalarWidth hr.scalarWidth hr.scalars hleft hr.blank
    (by simpa only [List.append_nil,descriptorReadyBank,FamilyDispatchInput.width] using hr.source) hr.count x y hx hy
  refine ⟨v',n,Zs,hu,hn,he,?_,ht⟩
  simpa only [FamilyDispatchApprox,FamilyDispatchInput.precision,FamilyDispatchInput.width,hr.outputBlank,List.append_nil] using ha

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

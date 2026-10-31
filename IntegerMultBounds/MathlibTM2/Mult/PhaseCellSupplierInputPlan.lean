module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedSupplierInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedJob

/-! A reusable physical input plan for mathematical packed jobs. Its readiness
contains only ordinary retained words and blank storage, never executions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure SupplierInputPlan (T : ℕ) where
  publication : PublicationInputPlan T
  work : Fin 325 → Fin T
  injective : Function.Injective work
  hprefix : ∀ i, work (Fin.castLE (by decide : 276 ≤ 325) i) = publication.work i
  masters : Fin 10 → Fin T
  parameters : Fin 8 → Fin T
  width : Fin T
  core : Fin T
  word : Fin T
  span : Fin T
  masterOff : ∀ i j, masters i ≠ work j
  masterTmp : ∀ i, masters i ≠ publication.retained 7
  retainedOff : ∀ i j, publication.retained i ≠ work j
  spanOff : ∀ j, span ≠ work j
  geometry : [masters 8,masters 9,publication.retained 1,PublicationInputPlan.factoryWork work 155,
    PublicationInputPlan.factoryWork work 165,PublicationInputPlan.factoryWork work 163,
    span,publication.retained 7,publication.retained 8].Nodup
  borrowed : ∀ i ∈ width::core::word::publication.retained 8::publication.retained 7::List.ofFn parameters,
    ∀ j, i ≠ work j
  coreRegs : [core,width,work 277,publication.retained 8,publication.retained 7].Nodup
  parameterRegs : ∀ i, [parameters i,width,word,publication.retained 8,publication.retained 7,work 324].Nodup

namespace PackedNormalizedJob
variable {A s : ℕ} [NeZero s]

noncomputable def factoryTarget (r : PackedNormalizedJob A s) : ℕ :=
  initialSchurTarget r.p r.u
    (boundaryTableBits r.p (boundaryRecoveryTarget r.p (r.targetOut+1)) 2
      (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card) 2

noncomputable def factoryMasters (r : PackedNormalizedJob A s) : Fin 10 → ℕ :=
  masterHeaderValues (2^15*r.p) (executionStagePrecision r.p r.l r.factoryTarget 2+1)
    (executionPrecision r.p r.l r.factoryTarget 2) r.l s r.t r.u (PhaseCellBand.width r.p r.u) r.a r.b

end PackedNormalizedJob
namespace SupplierInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

structure Ready (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : Prop where
  blank : ∀ i, S.R (plan.work i) = []
  left : ∀ i, S.L (plan.work i) = []
  masters : ∀ i, (S.R (plan.masters i)).length = r.factoryMasters i
  radius : (S.R (plan.publication.retained 0)).length = r.radius
  geometryWidth : (S.R (plan.publication.retained 1)).length = r.V
  headers : ∀ i, (S.R (plan.publication.headers i)).length = ![r.Fs.length,r.W,r.p,(r.b-r.a)*r.W] i
  payload : S.R (plan.publication.retained 6) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten
  tmp : S.R (plan.publication.retained 7) = []
  saved : S.R (plan.publication.retained 8) = []
  span : S.R plan.span = []
  parameters : ∀ i, (S.R (plan.parameters i)).length = ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] i
  width : (S.R plan.width).length = r.Bcore
  core : (S.R plan.core).length = coreLength s r.coreWidth r.k
  word : S.R plan.word = []

def program (plan : SupplierInputPlan T) : Pr P T Q A U :=
  plan.publication.fromHeaders plan.work plan.masters plan.parameters plan.width plan.core plan.word plan.span

def masterCost (plan : SupplierInputPlan T) (S : Stacks T A) : ℕ :=
  copyUnaryHeadersCost (fun i => (S.R i).length)
    (masterHeaderCopies (PublicationInputPlan.factoryWork plan.work ∘ packedFactoryNativeReg) plan.masters)

def headerCost (plan : SupplierInputPlan T) (S : Stacks T A) : ℕ :=
  copyUnaryHeadersCost (fun i => (S.R i).length) (descriptorHeaderCopies plan.publication.work plan.publication.headers)

noncomputable def timeCost (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : ℕ :=
  (plan.masterCost S+factoryGeometryCost r.a r.b r.V)+
    ((r.radius*(4*r.V+10)+4*r.V+8+(plan.headerCost S+
      (6*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+6)))+
      ((coreLength s r.coreWidth r.k+r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b)*(4*r.Bcore+10)+72*r.Bcore+109))

noncomputable def stock (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : ℕ :=
  (2*plan.masterCost S+(8*r.a+8*r.b+24*r.V+40))+
    ((2*(4*r.V+4)+(2*plan.headerCost S+
      2*(6*(cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten).length+6)))+10*(2*(4*r.Bcore+4)))

theorem exec (plan : SupplierInputPlan T) (r : PackedNormalizedJob A s)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready r S) (depth : ℕ) :
    ∃ v' n F, v'.user = v.user ∧ n ≤ plan.timeCost r S ∧
      (∀ i, F.R (plan.work i) = r.words i) ∧
      (∀ i, (∀ j, i ≠ plan.work j) → F.R i = S.R i) ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+plan.stock r S)
        depth plan.program (Host.mk v S) n (Host.mk v' F) := by
  obtain ⟨v',n,F,hu,hn,hbank,hframe,hleft,he⟩ := plan.publication.fromHeaders_exec (body := body)
    plan.work plan.injective plan.hprefix plan.masters plan.parameters plan.width plan.core plan.word plan.span
    plan.masterOff plan.masterTmp plan.retainedOff plan.spanOff plan.geometry plan.borrowed plan.coreRegs plan.parameterRegs
    (2^15*r.p) (executionStagePrecision r.p r.l r.factoryTarget 2+1)
    (executionPrecision r.p r.l r.factoryTarget 2) (PhaseCellBand.width r.p r.u)
    r.p r.W r.Fs.length ((r.b-r.a)*r.W) r.radius r.V r.u r.l r.targetOut s r.t r.a r.b r.Bcore
    (coreLength s r.coreWidth r.k) (cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten) v S
    hready.blank hready.left hready.masters hready.radius hready.geometryWidth hready.headers hready.payload
    hready.tmp hready.saved hready.span hready.parameters hready.width hready.core hready.word depth
  refine ⟨v',n,F,hu,hn,?_,hframe,hleft,?_,?_,he⟩
  · intro i
    have hwords := congrArg (fun C : Stacks 325 A => C.R i) hbank
    change F.R (plan.work i) = r.words i
    exact hwords.trans (by rfl)
  · exact congrArg (fun C : Stacks 325 A => C.inp) hbank
  · exact congrArg (fun C : Stacks 325 A => C.out) hbank

end SupplierInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

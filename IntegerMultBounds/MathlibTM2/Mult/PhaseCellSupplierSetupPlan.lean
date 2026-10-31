module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateSupplierReady

/-! Fixed register wiring for reusable per-call numerical-header generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure SupplierSetupPlan {T : ℕ} (input : SupplierInputPlan T) where
  mastersInjective : Function.Injective input.masters
  scalar : TblR 25 → Fin T
  scalarInjective : Function.Injective scalar
  word : Fin T
  saved : Fin T
  tmp : Fin T
  queue : Fin T
  carry : Fin T
  scalarOff : ∀ i r, scalar r ≠ input.masters i
  regs : ∀ i, [input.parameters i,scalar .wr,word,saved,tmp,queue].Nodup
  queueOff : ∀ r, scalar r ≠ queue
  scalarWidth : scalar .wr = input.width
  geometry : Fin 117 → Fin T
  geometryInjective : Function.Injective geometry
  precisionPort : geometry 114 = input.masters 0
  arithmeticPort : geometry 112 = input.masters 2
  periodPort : geometry 98 = input.masters 5
  parameterPort : geometry 99 = input.masters 6
  geometryDst : geometry 115 = input.publication.retained 1
  geometryOff : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], ∀ i, input.masters i ≠ geometry k
  baseOff : ∀ k ∈ input.baseSupport, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1

namespace SupplierSetupPlan
variable {T Q A s : ℕ} [NeZero s] {input : SupplierInputPlan T} {P U : Type} {body : P → Pr P T Q A U}

structure Ready (plan : SupplierSetupPlan input) (r : PackedNormalizedJob A s) (S : Stacks T A) : Prop where
  base : input.BaseReady r S
  scalarBlank : ∀ k : TblR 25, k ≠ .wr → S.R (plan.scalar k) = []
  mastersBlank : ∀ i, S.R (input.masters i) = []
  scratchBlank : ∀ k ∈ [plan.word,plan.saved,plan.tmp,plan.queue], S.R k = []
  geometryBlank : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], S.R (plan.geometry k) = []

def program (plan : SupplierSetupPlan input) : Pr P T Q A U :=
  supplierChangingHeaders plan.scalar input.parameters input.masters plan.word plan.saved plan.tmp plan.queue plan.carry plan.geometry

noncomputable def timeCost (r : PackedNormalizedJob A s) : ℕ :=
  (generateSupplierMastersCost r+(50*r.Bcore+51))+supplierGeometryWidthCost r

noncomputable def stock (r : PackedNormalizedJob A s) : ℕ :=
  ((392*r.Bcore+396)+3*(inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
    inverseMasterCopyCost r.Bcore r.factoryMasters))+
    (8*(8*r.q+9)+18*weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u)

theorem generate_exec (plan : SupplierSetupPlan input) (r : PackedNormalizedJob A s)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready r S) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ timeCost r ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+stock r) depth
        plan.program (Host.mk v S) n (Host.mk v' F) ∧ input.Ready r F ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, input.masters i ≠ k) → k ≠ input.publication.retained 1 → F.R k = S.R k :=
  input.generateReady_exec plan.mastersInjective plan.scalar plan.scalarInjective plan.scalarOff
    plan.word plan.saved plan.tmp plan.queue plan.carry plan.regs plan.queueOff plan.scalarWidth
    plan.geometry plan.geometryInjective plan.precisionPort plan.arithmeticPort plan.periodPort plan.parameterPort
    plan.geometryDst plan.geometryOff plan.baseOff r v S hready.base hready.scalarBlank hready.mastersBlank
    hready.scratchBlank hready.geometryBlank depth

def numericalRegs (input : SupplierInputPlan T) : List (Fin T) :=
  List.ofFn input.masters ++ [input.publication.retained 1]

theorem numericalRegs_nodup (plan : SupplierSetupPlan input) : (numericalRegs input).Nodup := by
  apply List.Nodup.append (List.nodup_ofFn_ofInjective plan.mastersInjective) (by simp)
  intro k hk hl
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
  have he : input.masters i = input.publication.retained 1 := by simpa using hl
  exact plan.geometryOff 115 (by simp) i (he.trans plan.geometryDst.symm)
end SupplierSetupPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

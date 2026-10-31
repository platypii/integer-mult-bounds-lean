module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierCoreStepStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierClassReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Generate one shared supplier payload counter from retained replica and
halo-symbol headers, preserving the class bank and all scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def supplierBatchCount (input : SupplierInputPlan T) (count saved tmp : Fin T) : Pr P T Q A U :=
  unaryProduct (input.publication.headers 0) (input.publication.headers 3) count saved tmp

noncomputable def supplierBatchCountCost (r : PackedNormalizedJob A s) : ℕ :=
  r.Fs.length*(4*((r.b-r.a)*r.W)+9)+4

theorem supplierBatchCount_exec_within (input : SupplierInputPlan T)
    (count saved tmp : Fin T)
    (hreg : [input.publication.headers 0,input.publication.headers 3,count,saved,tmp].Nodup)
    (r : PackedNormalizedJob A s) (v : HS T Q A U) (S : Stacks T A)
    (hclass : input.ClassReady r S) (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ supplierBatchCountCost r ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*supplierBatchCountCost r) depth
        (supplierBatchCount input count saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R count (List.replicate r.inputPayload.length tick)}) := by
  obtain ⟨v',n,hu,hn,he⟩ := unaryProduct_exec (body := body) hreg v S hsaved htmp
  have hreplicas : (S.R (input.publication.headers 0)).length = r.Fs.length := by simpa using hclass.headers 0
  have hsymbols : (S.R (input.publication.headers 3)).length = (r.b-r.a)*r.W := by simpa using hclass.headers 3
  rw [hreplicas,hsymbols] at hn he
  rw [hcount,List.append_nil,←Nat.mul_assoc,←PackedNormalizedJob.inputPayload_length] at he
  refine ⟨v',n,hu,hn,?_⟩
  exact mn_native_exec_within he 2 (unaryProduct_native _ _ _ _ _) depth _ (by
    have hm := Nat.mul_le_mul_left 2 hn
    dsimp only [supplierBatchCountCost] at *
    omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

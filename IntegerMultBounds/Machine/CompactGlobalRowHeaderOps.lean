import IntegerMultBounds.Machine.CompactGlobalRowHeaderPrimitives
import IntegerMultBounds.Machine.ActivePrefixStageHeadersOps

/-! Global reservation descriptors are runtime computations in a fixed finite
program. Fixed network constants are written physically; runtime exponents
never enter the finite program or its tape count. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowHeaderOps
noncomputable section
open ActiveRepairRankHeadersCommands (State bank caller put put_caller)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

inductive Op where
  | ordinary (op : ActivePrefixStageHeadersOps.Op)
  | power (base : ℕ) (focus : Fin 2 → Fin 28) (injective : Function.Injective focus)
  | logarithm (base : ℕ) (focus : Fin 2 → Fin 28) (injective : Function.Injective focus)
  | constant (value : ℕ) (dst : Fin 28)

def eval : Op → State → State
  | .ordinary op,st => ActivePrefixStageHeadersOps.eval op st
  | .power B f _,st => put st (f 1) (B^((st (f 0)).getD 0))
  | .logarithm B f _,st => put st (f 1) (Nat.clog B ((st (f 0)).getD 0))
  | .constant n dst,st => put st dst n

def valid : Op → State → Prop
  | .ordinary op,st => ActivePrefixStageHeadersOps.valid op st
  | .power B f _,st => 2≤B ∧ ∃ k, st (f 0)=some k ∧ st (f 1)=none
  | .logarithm B f _,st => 2≤B ∧ ∃ D, st (f 0)=some D ∧ st (f 1)=none ∧ 0<D
  | .constant _ dst,st => st dst=none

def program : Op → Σ k, Program 43 k a
  | .ordinary op => ActivePrefixStageHeadersOps.program op
  | .power B f hf => ⟨_,CompactGlobalRowHeaderPrimitives.powerProgram B f hf⟩
  | .logarithm B f hf => ⟨_,CompactGlobalRowHeaderPrimitives.logProgram B f hf⟩
  | .constant n dst => ⟨_,extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
      (FiniteReturnStackAt.placement dst)) 15⟩

def cost : Op → State → ℕ
  | .ordinary op,st => ActivePrefixStageHeadersOps.cost op st
  | .power B f _,st => FixedBasePowerDescriptor.constant B*B^((st (f 0)).getD 0)
  | .logarithm B f _,st => CompactGlobalRowHeaderPrimitives.logConstant B*((st (f 0)).getD 0)
  | .constant n _,_ => RecursiveChildQuotientsConstant.cost n

theorem runs (op : Op) (st : State) (hv : valid op st) :
    HoareTime (program (a := a) op).2 (fun x => x=bank st)
      (fun x => x=bank (eval op st)) (cost op st) := by
  cases op with
  | ordinary op => exact ActivePrefixStageHeadersOps.runs op st hv
  | power B f hf =>
    obtain ⟨hB,k,hk,hz⟩ := hv
    have h := CompactGlobalRowHeaderPrimitives.power B hB (caller (a := a) st) f hf
      (bits k) k (RecursiveChildQuotientsConstant.bits_value k) (RecursiveChildQuotientsConstant.bits_canonical k)
      (by simp [caller,hk]) (by simp [caller,hk]) (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hk,bank,put_caller,CompactGadgetReservationHeadersCore.bank] using h
  | logarithm B f hf =>
    obtain ⟨hB,D,hD,hz,hpos⟩ := hv
    have h := CompactGlobalRowHeaderPrimitives.logarithm B hB (caller (a := a) st) f hf
      (bits D) D hpos (RecursiveChildQuotientsConstant.bits_value D) (RecursiveChildQuotientsConstant.bits_canonical D)
      (by simp [caller,hD]) (by simp [caller,hD]) (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hD,bank,put_caller,CompactGadgetReservationHeadersCore.bank] using h
  | constant n dst =>
    change st dst=none at hv
    have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
      (FiniteReturnStackAt.placement dst) (caller (a := a) st)
      (by rw [FiniteReturnStackAt.active_bank]; simp [caller,hv])
    have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
        (FiniteReturnStackAt.placement dst)) (fun x => x=caller st)
        (fun x => x=caller (put st dst n)) (RecursiveChildQuotientsConstant.cost n) := by
      apply h.consequence (fun _ h => h) _ le_rfl
      rintro z ⟨small,rfl,rfl⟩
      rw [put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    simpa only [program,eval,cost,bank,CleanSubbank.bank] using hoare_extend_eq h' (SharedBank.empty 15 a)

def compile : List Op → Σ k, Program 43 k a
  | [] => ⟨1,skip 43 a (by decide)⟩
  | op::ops => ⟨_,seq (program op).2 (compile ops).2⟩
def execute : List Op → State → State
  | [],st => st
  | op::ops,st => execute ops (eval op st)
def validSchedule : List Op → State → Prop
  | [],_ => True
  | op::ops,st => valid op st ∧ validSchedule ops (eval op st)
def scheduleCost : List Op → State → ℕ
  | [],_ => 0
  | op::ops,st => cost op st+1+scheduleCost ops (eval op st)

theorem execute_append (xs ys : List Op) (st : State) :
    execute (xs++ys) st=execute ys (execute xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (eval x st)

theorem scheduleCost_append (xs ys : List Op) (st : State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih,Nat.add_assoc]

theorem schedule_runs (ops : List Op) (st : State) (hv : validSchedule ops st) :
    HoareTime (compile (a := a) ops).2 (fun x => x=bank st)
      (fun x => x=bank (execute ops st)) (scheduleCost ops st) := by
  induction ops generalizing st with
  | nil => exact skip_hoare (by decide) (bank st)
  | cons op ops ih => exact (runs op st hv.1).seq (ih (eval op st) hv.2)

end
end IntegerMultBounds.Machine.CompactGlobalRowHeaderOps

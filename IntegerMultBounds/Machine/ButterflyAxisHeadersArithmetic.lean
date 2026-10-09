import IntegerMultBounds.Machine.CompactChildHeadersArithmetic

/-! Clean power-of-two synthesis extends the fixed header arithmetic compiler.
Exponents are runtime descriptors; only the base two belongs to finite control. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersArithmetic
noncomputable section
open ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

inductive Op where
  | base (op : CompactChildHeadersArithmetic.Op)
  | power (focus : Fin 2 → Fin 28) (injective : Function.Injective focus)

def eval : Op → State → State
  | .base op,st => CompactChildHeadersArithmetic.eval op st
  | .power f _,st => put st (f 1) (2^((st (f 0)).getD 0))
def valid : Op → State → Prop
  | .base op,st => CompactChildHeadersArithmetic.valid op st
  | .power f _,st => ∃ n,st (f 0)=some n ∧ st (f 1)=none

def program : Op → Σ k,Program 43 k a
  | .base op => CompactChildHeadersArithmetic.program op
  | .power f hf => ⟨_,CompactGadgetReservationHeadersPowerRound.powerProgram f hf⟩
def cost : Op → State → ℕ
  | .base op,st => CompactChildHeadersArithmetic.cost op st
  | .power f _,st => FixedBasePowerDescriptor.constant 2*2^((st (f 0)).getD 0)

theorem runs (op : Op) (st : State) (hv : valid op st) :
    HoareTime (program (a:=a) op).2 (fun x => x=bank st)
      (fun x => x=bank (eval op st)) (cost op st) := by
  cases op with
  | base op => exact CompactChildHeadersArithmetic.runs op st hv
  | power f hf =>
    obtain ⟨n,hn,hz⟩ := hv
    have hh := CompactGadgetReservationHeadersPowerRound.power (caller (a:=a) st) f hf (bits n) n
      (RecursiveChildQuotientsConstant.bits_value n) (RecursiveChildQuotientsConstant.bits_canonical n)
      (by simp [caller,hn]) (by simp [caller,hn]) (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hn,bank,put_caller,CompactGadgetReservationHeadersCore.bank] using hh

def compile : List Op → Σ k,Program 43 k a
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

theorem schedule_runs (ops : List Op) (st : State) (hv : validSchedule ops st) :
    HoareTime (compile (a:=a) ops).2 (fun x => x=bank st)
      (fun x => x=bank (execute ops st)) (scheduleCost ops st) := by
  induction ops generalizing st with
  | nil => exact skip_hoare (by decide) (bank st)
  | cons op ops ih => exact (runs op st hv.1).seq (ih (eval op st) hv.2)

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersArithmetic

import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! Paid physical multiplication and rounding extend the fixed stage-header
arithmetic caller without changing its shared clean private workspace. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageHeadersOps
noncomputable section
open ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

inductive Op where
  | command (c : Command)
  | product (focus : Fin 3 → Fin 28) (injective : Function.Injective focus)
  | round (focus : Fin 3 → Fin 28) (injective : Function.Injective focus)
  | one (dst : Fin 28)

def eval : Op → State → State
  | .command c, st => ActiveRepairRankHeadersCommands.eval c st
  | .product f _, st => put st (f 2) ((st (f 1)).getD 0*(st (f 0)).getD 0)
  | .round f _, st => put st (f 2) (RoundedRowDescriptor.rounded ((st (f 0)).getD 0) ((st (f 1)).getD 0))
  | .one dst, st => put st dst 1

def valid : Op → State → Prop
  | .command c, st => ActiveRepairRankHeadersCommands.valid c st
  | .product f _, st => ∃ W N, st (f 0)=some W ∧ st (f 1)=some N ∧ st (f 2)=none ∧ 0<W
  | .round f _, st => ∃ R D, st (f 0)=some R ∧ st (f 1)=some D ∧ st (f 2)=none ∧ 0<R ∧ 0<D
  | .one dst, st => st dst=none

def program : Op → Σ k, Program 43 k a
  | .command c => ActiveRepairRankHeadersCommands.one c
  | .product f hf => ⟨_,CompactGadgetReservationHeadersCore.productProgram f hf⟩
  | .round f hf => ⟨_,CompactGadgetReservationHeadersPowerRound.roundProgram f hf⟩
  | .one dst => ⟨_,extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
      (FiniteReturnStackAt.placement dst)) 15⟩

def cost : Op → State → ℕ
  | .command c, st => ActiveRepairRankHeadersCommands.cost c st
  | .product f _, st => 53*((st (f 1)).getD 0*(st (f 0)).getD 0)+28
  | .round f _, st => 4096*RoundedRowDescriptor.rounded ((st (f 0)).getD 0) ((st (f 1)).getD 0)
  | .one _, _ => 12

theorem runs (op : Op) (st : State) (hv : valid op st) :
    HoareTime (program (a := a) op).2 (fun x => x=bank st)
      (fun x => x=bank (eval op st)) (cost op st) := by
  cases op with
  | command c => simpa only [program,eval,cost] using ActiveRepairRankHeadersCommands.runs (a := a) c st hv
  | product f hf =>
    obtain ⟨W,N,hW,hN,hz,hpos⟩ := hv
    have h := CompactGadgetReservationHeadersCore.product (caller (a := a) st) f hf
      (bits W) (bits N) N W hpos (RecursiveChildQuotientsConstant.bits_value W)
      (RecursiveChildQuotientsConstant.bits_value N) (RecursiveChildQuotientsConstant.bits_canonical W)
      (RecursiveChildQuotientsConstant.bits_canonical N)
      (by simp [caller,hW]) (by simp [caller,hW]) (by simp [caller,hN]) (by simp [caller,hN])
      (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hW,hN,bank,put_caller,CompactGadgetReservationHeadersCore.bank] using h
  | round f hf =>
    obtain ⟨R,D,hR,hD,hz,hposR,hposD⟩ := hv
    have h := CompactGadgetReservationHeadersPowerRound.round (caller (a := a) st) f hf
      (bits R) (bits D) R D hposR hposD (RecursiveChildQuotientsConstant.bits_value R)
      (RecursiveChildQuotientsConstant.bits_value D) (RecursiveChildQuotientsConstant.bits_canonical R)
      (RecursiveChildQuotientsConstant.bits_canonical D)
      (by simp [caller,hR]) (by simp [caller,hR]) (by simp [caller,hD]) (by simp [caller,hD])
      (by simp [caller,hz]) (by simp [caller,hz])
    simpa [program,eval,cost,hR,hD,bank,put_caller,CompactGadgetReservationHeadersCore.bank] using h
  | one dst =>
    change st dst=none at hv
    have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
      (FiniteReturnStackAt.placement dst) (caller (a := a) st)
      (by rw [FiniteReturnStackAt.active_bank]; simp [caller,hv])
    have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
        (FiniteReturnStackAt.placement dst)) (fun x => x=caller st)
        (fun x => x=caller (put st dst 1)) 12 := by
      apply h.consequence (fun _ h => h) _ (by decide)
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

theorem schedule_runs (ops : List Op) (st : State) (hv : validSchedule ops st) :
    HoareTime (compile (a := a) ops).2 (fun x => x=bank st)
      (fun x => x=bank (execute ops st)) (scheduleCost ops st) := by
  induction ops generalizing st with
  | nil => exact skip_hoare (by decide) (bank st)
  | cons op ops ih => exact (runs op st hv.1).seq (ih (eval op st) hv.2)

end
end IntegerMultBounds.Machine.ActivePrefixStageHeadersOps
